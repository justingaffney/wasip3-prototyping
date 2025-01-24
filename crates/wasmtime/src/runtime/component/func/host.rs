use crate::component::concurrent;
use crate::component::func::{LiftContext, LowerContext, Options};
use crate::component::matching::InstanceType;
use crate::component::storage::slice_to_storage_mut;
use crate::component::{ComponentNamedList, ComponentType, Lift, Lower, Val};
use crate::prelude::*;
use crate::runtime::vm::component::{
    ComponentInstance, InstanceFlags, VMComponentContext, VMLowering, VMLoweringCallee,
};
use crate::runtime::vm::{VMFuncRef, VMGlobalDefinition, VMMemoryDefinition, VMOpaqueContext};
use crate::{AsContextMut, CallHook, StoreContextMut, ValRaw};
use alloc::sync::Arc;
use core::any::Any;
use core::future::Future;
use core::iter;
use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;
use wasmtime_environ::component::{
    CanonicalAbiInfo, ComponentTypes, InterfaceType, RuntimeComponentInstanceIndex, StringEncoding,
    TypeFuncIndex, MAX_FLAT_PARAMS, MAX_FLAT_RESULTS,
};

#[cfg(feature = "component-model-async")]
use crate::runtime::vm::SendSyncPtr;

#[cfg(feature = "component-model-async")]
const STATUS_PARAMS_READ: u32 = 1;
#[cfg(feature = "component-model-async")]
const STATUS_DONE: u32 = 3;

struct Ptr<F>(*const F);

unsafe impl<F> Sync for Ptr<F> {}
unsafe impl<F> Send for Ptr<F> {}

pub struct HostFunc {
    entrypoint: VMLoweringCallee,
    typecheck: Box<dyn (Fn(TypeFuncIndex, &InstanceType<'_>) -> Result<()>) + Send + Sync>,
    func: Box<dyn Any + Send + Sync>,
}

impl HostFunc {
    pub(crate) fn from_closure<T, F, P, R>(func: F) -> Arc<HostFunc>
    where
        F: Fn(StoreContextMut<T>, P) -> Result<R> + Send + Sync + 'static,
        P: ComponentNamedList + Lift + 'static,
        R: ComponentNamedList + Lower + Send + Sync + 'static,
    {
        Self::from_concurrent(move |store, params| {
            let result = func(store, params);
            async move { concurrent::for_any(move |_| result) }
        })
    }

    pub(crate) fn from_concurrent<T, F, N, FN, P, R>(func: F) -> Arc<HostFunc>
    where
        N: FnOnce(StoreContextMut<T>) -> Result<R> + Send + Sync + 'static,
        FN: Future<Output = N> + Send + Sync + 'static,
        F: Fn(StoreContextMut<T>, P) -> FN + Send + Sync + 'static,
        P: ComponentNamedList + Lift + 'static,
        R: ComponentNamedList + Lower + Send + Sync + 'static,
    {
        let entrypoint = Self::entrypoint::<T, F, N, FN, P, R>;
        Arc::new(HostFunc {
            entrypoint,
            typecheck: Box::new(typecheck::<P, R>),
            func: Box::new(func),
        })
    }

    extern "C" fn entrypoint<T, F, N, FN, P, R>(
        cx: NonNull<VMOpaqueContext>,
        data: NonNull<u8>,
        ty: u32,
        caller_instance: u32,
        flags: NonNull<VMGlobalDefinition>,
        memory: *mut VMMemoryDefinition,
        realloc: *mut VMFuncRef,
        string_encoding: u8,
        async_: u8,
        storage: NonNull<MaybeUninit<ValRaw>>,
        storage_len: usize,
    ) -> bool
    where
        N: FnOnce(StoreContextMut<T>) -> Result<R> + Send + Sync + 'static,
        FN: Future<Output = N> + Send + Sync + 'static,
        F: Fn(StoreContextMut<T>, P) -> FN + Send + Sync + 'static,
        P: ComponentNamedList + Lift + 'static,
        R: ComponentNamedList + Lower + Send + Sync + 'static,
    {
        let data = Ptr(data.as_ptr() as *const F);
        unsafe {
            call_host_and_handle_result::<T>(cx, |instance, types, store| {
                call_host(
                    instance,
                    types,
                    store,
                    TypeFuncIndex::from_u32(ty),
                    RuntimeComponentInstanceIndex::from_u32(caller_instance),
                    InstanceFlags::from_raw(flags),
                    memory,
                    realloc,
                    StringEncoding::from_u8(string_encoding).unwrap(),
                    async_ != 0,
                    NonNull::slice_from_raw_parts(storage, storage_len).as_mut(),
                    move |store, args| (*data.0)(store, args),
                )
            })
        }
    }

    pub(crate) fn new_dynamic<T, F>(func: F) -> Arc<HostFunc>
    where
        F: Fn(StoreContextMut<'_, T>, &[Val], &mut [Val]) -> Result<()> + Send + Sync + 'static,
    {
        Self::new_dynamic_concurrent(move |store, params: Vec<Val>, result_count| {
            let mut results = iter::repeat(Val::Bool(false))
                .take(result_count)
                .collect::<Vec<_>>();
            let result = func(store, &params, &mut results);
            let result = result.map(move |()| results);
            async move { concurrent::for_any(move |_| result) }
        })
    }

    pub(crate) fn new_dynamic_concurrent<T, F, N, FN>(f: F) -> Arc<HostFunc>
    where
        N: FnOnce(StoreContextMut<T>) -> Result<Vec<Val>> + Send + Sync + 'static,
        FN: Future<Output = N> + Send + Sync + 'static,
        F: Fn(StoreContextMut<T>, Vec<Val>, usize) -> FN + Send + Sync + 'static,
    {
        Arc::new(HostFunc {
            entrypoint: dynamic_entrypoint::<T, F, N, FN>,
            // This function performs dynamic type checks and subsequently does
            // not need to perform up-front type checks. Instead everything is
            // dynamically managed at runtime.
            typecheck: Box::new(move |_expected_index, _expected_types| Ok(())),
            func: Box::new(f),
        })
    }

    pub fn typecheck(&self, ty: TypeFuncIndex, types: &InstanceType<'_>) -> Result<()> {
        (self.typecheck)(ty, types)
    }

    pub fn lowering(&self) -> VMLowering {
        let data = NonNull::from(&*self.func).cast();
        VMLowering {
            callee: self.entrypoint,
            data: data.into(),
        }
    }
}

fn typecheck<P, R>(ty: TypeFuncIndex, types: &InstanceType<'_>) -> Result<()>
where
    P: ComponentNamedList + Lift,
    R: ComponentNamedList + Lower,
{
    let ty = &types.types[ty];
    P::typecheck(&InterfaceType::Tuple(ty.params), types)
        .context("type mismatch with parameters")?;
    R::typecheck(&InterfaceType::Tuple(ty.results), types).context("type mismatch with results")?;
    Ok(())
}

/// The "meat" of calling a host function from wasm.
///
/// This function is delegated to from implementations of
/// `HostFunc::from_closure`. Most of the arguments from the `entrypoint` are
/// forwarded here except for the `data` pointer which is encapsulated in the
/// `closure` argument here.
///
/// This function is parameterized over:
///
/// * `T` - the type of store this function works with (an unsafe assertion)
/// * `Params` - the parameters to the host function, viewed as a tuple
/// * `Return` - the result of the host function
/// * `F` - the `closure` to actually receive the `Params` and return the
///   `Return`
///
/// It's expected that `F` will "un-tuple" the arguments to pass to a host
/// closure.
///
/// This function is in general `unsafe` as the validity of all the parameters
/// must be upheld. Generally that's done by ensuring this is only called from
/// the select few places it's intended to be called from.
unsafe fn call_host<T, Params, Return, F, N, FN>(
    instance: *mut ComponentInstance,
    types: &Arc<ComponentTypes>,
    mut cx: StoreContextMut<'_, T>,
    ty: TypeFuncIndex,
    caller_instance: RuntimeComponentInstanceIndex,
    mut flags: InstanceFlags,
    memory: *mut VMMemoryDefinition,
    realloc: *mut VMFuncRef,
    string_encoding: StringEncoding,
    async_: bool,
    storage: &mut [MaybeUninit<ValRaw>],
    closure: F,
) -> Result<()>
where
    N: FnOnce(StoreContextMut<T>) -> Result<Return> + Send + Sync + 'static,
    FN: Future<Output = N> + Send + Sync + 'static,
    F: Fn(StoreContextMut<T>, Params) -> FN + 'static,
    Params: Lift,
    Return: Lower + Send + Sync + 'static,
{
    /// Representation of arguments to this function when a return pointer is in
    /// use, namely the argument list is followed by a single value which is the
    /// return pointer.
    #[repr(C)]
    struct ReturnPointer<T> {
        args: T,
        retptr: ValRaw,
    }

    /// Representation of arguments to this function when the return value is
    /// returned directly, namely the arguments and return value all start from
    /// the beginning (aka this is a `union`, not a `struct`).
    #[repr(C)]
    union ReturnStack<T: Copy, U: Copy> {
        args: T,
        ret: U,
    }

    let options = Options::new(
        cx.0.id(),
        NonNull::new(memory),
        NonNull::new(realloc),
        string_encoding,
        async_,
        None,
    );

    // Perform a dynamic check that this instance can indeed be left. Exiting
    // the component is disallowed, for example, when the `realloc` function
    // calls a canonical import.
    if !flags.may_leave() {
        bail!("cannot leave component instance");
    }

    let ty = &types[ty];
    let param_tys = InterfaceType::Tuple(ty.params);
    let result_tys = InterfaceType::Tuple(ty.results);

    if async_ {
        #[cfg(feature = "component-model-async")]
        {
            let paramptr = storage[0].assume_init();
            let retptr = storage[1].assume_init();

            let params = {
                let lift = &mut LiftContext::new(cx.0, &options, types, instance);
                lift.enter_call();
                let ptr = validate_inbounds::<Params>(lift.memory(), &paramptr)?;
                Params::load(lift, param_tys, &lift.memory()[ptr..][..Params::SIZE32])?
            };

            let future = closure(cx.as_context_mut(), params);

            let task =
                concurrent::first_poll(instance, cx.as_context_mut(), future, caller_instance, {
                    let types = types.clone();
                    let instance = SendSyncPtr::new(NonNull::new(instance).unwrap());
                    move |cx, ret: Return| {
                        let mut lower = LowerContext::new(cx, &options, &types, instance.as_ptr());
                        let ptr = validate_inbounds::<Return>(lower.as_slice_mut(), &retptr)?;
                        ret.store(&mut lower, result_tys, ptr)
                    }
                })?;

            let status = if let Some(task) = task {
                (STATUS_PARAMS_READ << 30) | task
            } else {
                STATUS_DONE << 30
            };

            storage[0] = MaybeUninit::new(ValRaw::i32(status as i32));
        }
        #[cfg(not(feature = "component-model-async"))]
        {
            unreachable!(
                "async-lowered imports should have failed validation \
                 when `component-model-async` feature disabled"
            );
        }
    } else {
        // There's a 2x2 matrix of whether parameters and results are stored on the
        // stack or on the heap. Each of the 4 branches here have a different
        // representation of the storage of arguments/returns.
        //
        // Also note that while four branches are listed here only one is taken for
        // any particular `Params` and `Return` combination. This should be
        // trivially DCE'd by LLVM. Perhaps one day with enough const programming in
        // Rust we can make monomorphizations of this function codegen only one
        // branch, but today is not that day.
        let mut storage: Storage<'_, Params, Return> = if Params::flatten_count() <= MAX_FLAT_PARAMS
        {
            if Return::flatten_count() <= MAX_FLAT_RESULTS {
                Storage::Direct(slice_to_storage_mut(storage))
            } else {
                Storage::ResultsIndirect(slice_to_storage_mut(storage).assume_init_ref())
            }
        } else {
            if Return::flatten_count() <= MAX_FLAT_RESULTS {
                Storage::ParamsIndirect(slice_to_storage_mut(storage))
            } else {
                Storage::Indirect(slice_to_storage_mut(storage).assume_init_ref())
            }
        };
        let mut lift = LiftContext::new(cx.0, &options, types, instance);
        lift.enter_call();
        let params = storage.lift_params(&mut lift, param_tys)?;

        let future = closure(cx.as_context_mut(), params);

        let (ret, cx) = concurrent::poll_and_block(cx, future, caller_instance)?;

        flags.set_may_leave(false);
        let mut lower = LowerContext::new(cx, &options, types, instance);
        storage.lower_results(&mut lower, result_tys, ret)?;
        flags.set_may_leave(true);
        lower.exit_call()?;
    }

    return Ok(());

    enum Storage<'a, P: ComponentType, R: ComponentType> {
        Direct(&'a mut MaybeUninit<ReturnStack<P::Lower, R::Lower>>),
        ParamsIndirect(&'a mut MaybeUninit<ReturnStack<ValRaw, R::Lower>>),
        ResultsIndirect(&'a ReturnPointer<P::Lower>),
        Indirect(&'a ReturnPointer<ValRaw>),
    }

    impl<P, R> Storage<'_, P, R>
    where
        P: ComponentType + Lift,
        R: ComponentType + Lower,
    {
        unsafe fn lift_params(&self, cx: &mut LiftContext<'_>, ty: InterfaceType) -> Result<P> {
            match self {
                Storage::Direct(storage) => P::lift(cx, ty, &storage.assume_init_ref().args),
                Storage::ResultsIndirect(storage) => P::lift(cx, ty, &storage.args),
                Storage::ParamsIndirect(storage) => {
                    let ptr = validate_inbounds::<P>(cx.memory(), &storage.assume_init_ref().args)?;
                    P::load(cx, ty, &cx.memory()[ptr..][..P::SIZE32])
                }
                Storage::Indirect(storage) => {
                    let ptr = validate_inbounds::<P>(cx.memory(), &storage.args)?;
                    P::load(cx, ty, &cx.memory()[ptr..][..P::SIZE32])
                }
            }
        }

        unsafe fn lower_results<T>(
            &mut self,
            cx: &mut LowerContext<'_, T>,
            ty: InterfaceType,
            ret: R,
        ) -> Result<()> {
            match self {
                Storage::Direct(storage) => ret.lower(cx, ty, map_maybe_uninit!(storage.ret)),
                Storage::ParamsIndirect(storage) => {
                    ret.lower(cx, ty, map_maybe_uninit!(storage.ret))
                }
                Storage::ResultsIndirect(storage) => {
                    let ptr = validate_inbounds::<R>(cx.as_slice_mut(), &storage.retptr)?;
                    ret.store(cx, ty, ptr)
                }
                Storage::Indirect(storage) => {
                    let ptr = validate_inbounds::<R>(cx.as_slice_mut(), &storage.retptr)?;
                    ret.store(cx, ty, ptr)
                }
            }
        }
    }
}

pub(crate) fn validate_inbounds<T: ComponentType>(memory: &[u8], ptr: &ValRaw) -> Result<usize> {
    // FIXME(#4311): needs memory64 support
    let ptr = usize::try_from(ptr.get_u32())?;
    if ptr % usize::try_from(T::ALIGN32)? != 0 {
        bail!("pointer not aligned");
    }
    let end = match ptr.checked_add(T::SIZE32) {
        Some(n) => n,
        None => bail!("pointer size overflow"),
    };
    if end > memory.len() {
        bail!("pointer out of bounds")
    }
    Ok(ptr)
}

unsafe fn call_host_and_handle_result<T>(
    cx: NonNull<VMOpaqueContext>,
    func: impl FnOnce(
        *mut ComponentInstance,
        &Arc<ComponentTypes>,
        StoreContextMut<'_, T>,
    ) -> Result<()>,
) -> bool {
    let cx = VMComponentContext::from_opaque(cx);
    let instance = cx.as_ref().instance();
    let types = (*instance).component_types();
    let raw_store = (*instance).store();
    let mut store = StoreContextMut(&mut *raw_store.cast());

    crate::runtime::vm::catch_unwind_and_record_trap(|| {
        store.0.call_hook(CallHook::CallingHost)?;
        let res = func(instance, types, store.as_context_mut());
        store.0.call_hook(CallHook::ReturningFromHost)?;
        res
    })
}

unsafe fn call_host_dynamic<T, F, N, FN>(
    instance: *mut ComponentInstance,
    types: &Arc<ComponentTypes>,
    mut store: StoreContextMut<'_, T>,
    ty: TypeFuncIndex,
    caller_instance: RuntimeComponentInstanceIndex,
    mut flags: InstanceFlags,
    memory: *mut VMMemoryDefinition,
    realloc: *mut VMFuncRef,
    string_encoding: StringEncoding,
    async_: bool,
    storage: &mut [MaybeUninit<ValRaw>],
    closure: F,
) -> Result<()>
where
    N: FnOnce(StoreContextMut<T>) -> Result<Vec<Val>> + Send + Sync + 'static,
    FN: Future<Output = N> + Send + Sync + 'static,
    F: Fn(StoreContextMut<T>, Vec<Val>, usize) -> FN + 'static,
{
    let options = Options::new(
        store.0.id(),
        NonNull::new(memory),
        NonNull::new(realloc),
        string_encoding,
        async_,
        None,
    );

    // Perform a dynamic check that this instance can indeed be left. Exiting
    // the component is disallowed, for example, when the `realloc` function
    // calls a canonical import.
    if !flags.may_leave() {
        bail!("cannot leave component instance");
    }

    let args;
    let ret_index;

    let func_ty = &types[ty];
    let param_tys = &types[func_ty.params];
    let result_tys = &types[func_ty.results];

    if async_ {
        #[cfg(feature = "component-model-async")]
        {
            let paramptr = storage[0].assume_init();
            let retptr = storage[1].assume_init();

            let params = {
                let mut lift = &mut LiftContext::new(store.0, &options, types, instance);
                lift.enter_call();
                let mut offset =
                    validate_inbounds_dynamic(&param_tys.abi, lift.memory(), &paramptr)?;
                param_tys
                    .types
                    .iter()
                    .map(|ty| {
                        let abi = types.canonical_abi(ty);
                        let size = usize::try_from(abi.size32).unwrap();
                        let memory = &lift.memory()[abi.next_field32_size(&mut offset)..][..size];
                        Val::load(&mut lift, *ty, memory)
                    })
                    .collect::<Result<Vec<_>>>()?
            };

            let future = closure(store.as_context_mut(), params, result_tys.types.len());

            let task = concurrent::first_poll(
                instance,
                store.as_context_mut(),
                future,
                caller_instance,
                {
                    let types = types.clone();
                    let instance = SendSyncPtr::new(NonNull::new(instance).unwrap());
                    let result_tys = func_ty.results;
                    move |store, result_vals: Vec<Val>| {
                        let result_tys = &types[result_tys];
                        if result_vals.len() != result_tys.types.len() {
                            bail!("result length mismatch");
                        }

                        let mut lower =
                            LowerContext::new(store, &options, &types, instance.as_ptr());
                        let mut ptr = validate_inbounds_dynamic(
                            &result_tys.abi,
                            lower.as_slice_mut(),
                            &retptr,
                        )?;
                        for (val, ty) in result_vals.iter().zip(result_tys.types.iter()) {
                            let offset = types.canonical_abi(ty).next_field32_size(&mut ptr);
                            val.store(&mut lower, *ty, offset)?;
                        }
                        Ok(())
                    }
                },
            )?;

            let status = if let Some(task) = task {
                (STATUS_PARAMS_READ << 30) | task
            } else {
                STATUS_DONE << 30
            };

            storage[0] = MaybeUninit::new(ValRaw::i32(status as i32));
        }
        #[cfg(not(feature = "component-model-async"))]
        {
            unreachable!(
                "async-lowered imports should have failed validation \
                 when `component-model-async` feature disabled"
            );
        }
    } else {
        let mut cx = LiftContext::new(store.0, &options, types, instance);
        cx.enter_call();
        if let Some(param_count) = param_tys.abi.flat_count(MAX_FLAT_PARAMS) {
            // NB: can use `MaybeUninit::slice_assume_init_ref` when that's stable
            let mut iter =
                mem::transmute::<&[MaybeUninit<ValRaw>], &[ValRaw]>(&storage[..param_count]).iter();
            args = param_tys
                .types
                .iter()
                .map(|ty| Val::lift(&mut cx, *ty, &mut iter))
                .collect::<Result<Vec<_>>>()?;
            ret_index = param_count;
            assert!(iter.next().is_none());
        } else {
            let mut offset = validate_inbounds_dynamic(
                &param_tys.abi,
                cx.memory(),
                storage[0].assume_init_ref(),
            )?;
            args = param_tys
                .types
                .iter()
                .map(|ty| {
                    let abi = types.canonical_abi(ty);
                    let size = usize::try_from(abi.size32).unwrap();
                    let memory = &cx.memory()[abi.next_field32_size(&mut offset)..][..size];
                    Val::load(&mut cx, *ty, memory)
                })
                .collect::<Result<Vec<_>>>()?;
            ret_index = 1;
        };

        let future = closure(store.as_context_mut(), args, result_tys.types.len());
        let (result_vals, store) = concurrent::poll_and_block(store, future, caller_instance)?;

        flags.set_may_leave(false);

        let mut cx = LowerContext::new(store, &options, types, instance);
        if let Some(cnt) = result_tys.abi.flat_count(MAX_FLAT_RESULTS) {
            let mut dst = storage[..cnt].iter_mut();
            for (val, ty) in result_vals.iter().zip(result_tys.types.iter()) {
                val.lower(&mut cx, *ty, &mut dst)?;
            }
            assert!(dst.next().is_none());
        } else {
            let ret_ptr = storage[ret_index].assume_init_ref();
            let mut ptr = validate_inbounds_dynamic(&result_tys.abi, cx.as_slice_mut(), ret_ptr)?;
            for (val, ty) in result_vals.iter().zip(result_tys.types.iter()) {
                let offset = types.canonical_abi(ty).next_field32_size(&mut ptr);
                val.store(&mut cx, *ty, offset)?;
            }
        }

        flags.set_may_leave(true);

        cx.exit_call()?;
    }

    return Ok(());
}

pub(crate) fn validate_inbounds_dynamic(
    abi: &CanonicalAbiInfo,
    memory: &[u8],
    ptr: &ValRaw,
) -> Result<usize> {
    // FIXME(#4311): needs memory64 support
    let ptr = usize::try_from(ptr.get_u32())?;
    if ptr % usize::try_from(abi.align32)? != 0 {
        bail!("pointer not aligned");
    }
    let end = match ptr.checked_add(usize::try_from(abi.size32).unwrap()) {
        Some(n) => n,
        None => bail!("pointer size overflow"),
    };
    if end > memory.len() {
        bail!("pointer out of bounds")
    }
    Ok(ptr)
}

extern "C" fn dynamic_entrypoint<T, F, N, FN>(
    cx: NonNull<VMOpaqueContext>,
    data: NonNull<u8>,
    ty: u32,
    caller_instance: u32,
    flags: NonNull<VMGlobalDefinition>,
    memory: *mut VMMemoryDefinition,
    realloc: *mut VMFuncRef,
    string_encoding: u8,
    async_: u8,
    storage: NonNull<MaybeUninit<ValRaw>>,
    storage_len: usize,
) -> bool
where
    N: FnOnce(StoreContextMut<T>) -> Result<Vec<Val>> + Send + Sync + 'static,
    FN: Future<Output = N> + Send + Sync + 'static,
    F: Fn(StoreContextMut<T>, Vec<Val>, usize) -> FN + Send + Sync + 'static,
{
    let data = Ptr(data.as_ptr() as *const F);
    unsafe {
        call_host_and_handle_result(cx, |instance, types, store| {
            call_host_dynamic(
                instance,
                types,
                store,
                TypeFuncIndex::from_u32(ty),
                RuntimeComponentInstanceIndex::from_u32(caller_instance),
                InstanceFlags::from_raw(flags),
                memory,
                realloc,
                StringEncoding::from_u8(string_encoding).unwrap(),
                async_ != 0,
                NonNull::slice_from_raw_parts(storage, storage_len).as_mut(),
                move |store, params, results| (*data.0)(store, params, results),
            )
        })
    }
}
