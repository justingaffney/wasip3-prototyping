/// Auto-generated bindings for a pre-instantiated version of a
/// component which implements the world `the-world`.
///
/// This structure is created through [`TheWorldPre::new`] which
/// takes a [`InstancePre`](wasmtime::component::InstancePre) that
/// has been created through a [`Linker`](wasmtime::component::Linker).
///
/// For more information see [`TheWorld`] as well.
pub struct TheWorldPre<T> {
    instance_pre: wasmtime::component::InstancePre<T>,
    indices: TheWorldIndices,
}
impl<T> Clone for TheWorldPre<T> {
    fn clone(&self) -> Self {
        Self {
            instance_pre: self.instance_pre.clone(),
            indices: self.indices.clone(),
        }
    }
}
impl<_T> TheWorldPre<_T> {
    /// Creates a new copy of `TheWorldPre` bindings which can then
    /// be used to instantiate into a particular store.
    ///
    /// This method may fail if the component behind `instance_pre`
    /// does not have the required exports.
    pub fn new(
        instance_pre: wasmtime::component::InstancePre<_T>,
    ) -> wasmtime::Result<Self> {
        let indices = TheWorldIndices::new(instance_pre.component())?;
        Ok(Self { instance_pre, indices })
    }
    pub fn engine(&self) -> &wasmtime::Engine {
        self.instance_pre.engine()
    }
    pub fn instance_pre(&self) -> &wasmtime::component::InstancePre<_T> {
        &self.instance_pre
    }
    /// Instantiates a new instance of [`TheWorld`] within the
    /// `store` provided.
    ///
    /// This function will use `self` as the pre-instantiated
    /// instance to perform instantiation. Afterwards the preloaded
    /// indices in `self` are used to lookup all exports on the
    /// resulting instance.
    pub async fn instantiate_async(
        &self,
        mut store: impl wasmtime::AsContextMut<Data = _T>,
    ) -> wasmtime::Result<TheWorld>
    where
        _T: Send,
    {
        let mut store = store.as_context_mut();
        let instance = self.instance_pre.instantiate_async(&mut store).await?;
        self.indices.load(&mut store, &instance)
    }
}
/// Auto-generated bindings for index of the exports of
/// `the-world`.
///
/// This is an implementation detail of [`TheWorldPre`] and can
/// be constructed if needed as well.
///
/// For more information see [`TheWorld`] as well.
#[derive(Clone)]
pub struct TheWorldIndices {
    interface0: exports::foo::foo::floats::GuestIndices,
}
/// Auto-generated bindings for an instance a component which
/// implements the world `the-world`.
///
/// This structure can be created through a number of means
/// depending on your requirements and what you have on hand:
///
/// * The most convenient way is to use
///   [`TheWorld::instantiate_async`] which only needs a
///   [`Store`], [`Component`], and [`Linker`].
///
/// * Alternatively you can create a [`TheWorldPre`] ahead of
///   time with a [`Component`] to front-load string lookups
///   of exports once instead of per-instantiation. This
///   method then uses [`TheWorldPre::instantiate_async`] to
///   create a [`TheWorld`].
///
/// * If you've instantiated the instance yourself already
///   then you can use [`TheWorld::new`].
///
/// * You can also access the guts of instantiation through
///   [`TheWorldIndices::new_instance`] followed
///   by [`TheWorldIndices::load`] to crate an instance of this
///   type.
///
/// These methods are all equivalent to one another and move
/// around the tradeoff of what work is performed when.
///
/// [`Store`]: wasmtime::Store
/// [`Component`]: wasmtime::component::Component
/// [`Linker`]: wasmtime::component::Linker
pub struct TheWorld {
    interface0: exports::foo::foo::floats::Guest,
}
const _: () = {
    #[allow(unused_imports)]
    use wasmtime::component::__internal::anyhow;
    impl TheWorldIndices {
        /// Creates a new copy of `TheWorldIndices` bindings which can then
        /// be used to instantiate into a particular store.
        ///
        /// This method may fail if the component does not have the
        /// required exports.
        pub fn new(
            component: &wasmtime::component::Component,
        ) -> wasmtime::Result<Self> {
            let _component = component;
            let interface0 = exports::foo::foo::floats::GuestIndices::new(_component)?;
            Ok(TheWorldIndices { interface0 })
        }
        /// Creates a new instance of [`TheWorldIndices`] from an
        /// instantiated component.
        ///
        /// This method of creating a [`TheWorld`] will perform string
        /// lookups for all exports when this method is called. This
        /// will only succeed if the provided instance matches the
        /// requirements of [`TheWorld`].
        pub fn new_instance(
            mut store: impl wasmtime::AsContextMut,
            instance: &wasmtime::component::Instance,
        ) -> wasmtime::Result<Self> {
            let _instance = instance;
            let interface0 = exports::foo::foo::floats::GuestIndices::new_instance(
                &mut store,
                _instance,
            )?;
            Ok(TheWorldIndices { interface0 })
        }
        /// Uses the indices stored in `self` to load an instance
        /// of [`TheWorld`] from the instance provided.
        ///
        /// Note that at this time this method will additionally
        /// perform type-checks of all exports.
        pub fn load(
            &self,
            mut store: impl wasmtime::AsContextMut,
            instance: &wasmtime::component::Instance,
        ) -> wasmtime::Result<TheWorld> {
            let _instance = instance;
            let interface0 = self.interface0.load(&mut store, &_instance)?;
            Ok(TheWorld { interface0 })
        }
    }
    impl TheWorld {
        /// Convenience wrapper around [`TheWorldPre::new`] and
        /// [`TheWorldPre::instantiate_async`].
        pub async fn instantiate_async<_T>(
            mut store: impl wasmtime::AsContextMut<Data = _T>,
            component: &wasmtime::component::Component,
            linker: &wasmtime::component::Linker<_T>,
        ) -> wasmtime::Result<TheWorld>
        where
            _T: Send,
        {
            let pre = linker.instantiate_pre(component)?;
            TheWorldPre::new(pre)?.instantiate_async(store).await
        }
        /// Convenience wrapper around [`TheWorldIndices::new_instance`] and
        /// [`TheWorldIndices::load`].
        pub fn new(
            mut store: impl wasmtime::AsContextMut,
            instance: &wasmtime::component::Instance,
        ) -> wasmtime::Result<TheWorld> {
            let indices = TheWorldIndices::new_instance(&mut store, instance)?;
            indices.load(store, instance)
        }
        pub fn foo_foo_floats(&self) -> &exports::foo::foo::floats::Guest {
            &self.interface0
        }
    }
};
pub mod foo {
    pub mod foo {
        #[allow(clippy::all)]
        pub mod floats {
            #[allow(unused_imports)]
            use wasmtime::component::__internal::{anyhow, Box};
            #[wasmtime::component::__internal::trait_variant_make(::core::marker::Send)]
            pub trait Host: Send {
                fn f32_param<T: 'static>(
                    accessor: &mut wasmtime::component::Accessor<T, Self>,
                    x: f32,
                ) -> impl ::core::future::Future<Output = ()> + Send + Sync
                where
                    Self: Sized;
                fn f64_param<T: 'static>(
                    accessor: &mut wasmtime::component::Accessor<T, Self>,
                    x: f64,
                ) -> impl ::core::future::Future<Output = ()> + Send + Sync
                where
                    Self: Sized;
                fn f32_result<T: 'static>(
                    accessor: &mut wasmtime::component::Accessor<T, Self>,
                ) -> impl ::core::future::Future<Output = f32> + Send + Sync
                where
                    Self: Sized;
                fn f64_result<T: 'static>(
                    accessor: &mut wasmtime::component::Accessor<T, Self>,
                ) -> impl ::core::future::Future<Output = f64> + Send + Sync
                where
                    Self: Sized;
            }
            thread_local! {
                static HOST : std::cell::Cell <* mut u8 > =
                std::cell::Cell::new(std::ptr::null_mut()); static SPAWNED :
                std::cell::RefCell < Vec < wasmtime::component::__internal::Spawned >> =
                std::cell::RefCell::new(Vec::new());
            }
            fn poll<T, G: for<'a> GetHost<&'a mut T>, F: std::future::Future + ?Sized>(
                getter: G,
                store: wasmtime::VMStoreRawPtr,
                cx: &mut std::task::Context,
                future: std::pin::Pin<&mut F>,
            ) -> std::task::Poll<F::Output> {
                use wasmtime::component::__internal::SpawnedInner;
                use std::mem;
                use std::ops::DerefMut;
                use std::task::Poll;
                struct ResetHost(*mut u8);
                impl Drop for ResetHost {
                    fn drop(&mut self) {
                        HOST.with(|v| v.set(self.0))
                    }
                }
                struct ClearSpawned;
                impl Drop for ClearSpawned {
                    fn drop(&mut self) {
                        SPAWNED.with(|v| v.borrow_mut().clear())
                    }
                }
                let mut store_cx = unsafe {
                    wasmtime::StoreContextMut::new(&mut *store.0.as_ptr().cast())
                };
                let _clear = ClearSpawned;
                let result = {
                    let host = &mut getter(store_cx.data_mut());
                    let old = HOST.with(|v| v.replace((host as *mut G::Host).cast()));
                    let _reset = ResetHost(old);
                    future.poll(cx)
                };
                for spawned in SPAWNED
                    .with(|v| { mem::take(DerefMut::deref_mut(&mut v.borrow_mut())) })
                {
                    store_cx
                        .spawn(
                            wasmtime::component::__internal::poll_fn(move |cx| {
                                let mut spawned = spawned.try_lock().unwrap();
                                let inner = mem::replace(
                                    DerefMut::deref_mut(&mut spawned),
                                    SpawnedInner::Aborted,
                                );
                                if let SpawnedInner::Unpolled(mut future)
                                | SpawnedInner::Polled { mut future, .. } = inner {
                                    let result = poll(getter, store, cx, future.as_mut());
                                    *DerefMut::deref_mut(&mut spawned) = SpawnedInner::Polled {
                                        future,
                                        waker: cx.waker().clone(),
                                    };
                                    result
                                } else {
                                    Poll::Ready(Ok(()))
                                }
                            }),
                        )
                }
                result
            }
            pub trait GetHost<
                T,
            >: Fn(T) -> <Self as GetHost<T>>::Host + Send + Sync + Copy + 'static {
                type Host: Host + Send;
            }
            impl<F, T, O> GetHost<T> for F
            where
                F: Fn(T) -> O + Send + Sync + Copy + 'static,
                O: Host + Send,
            {
                type Host = O;
            }
            pub fn add_to_linker_get_host<
                T,
                G: for<'a> GetHost<&'a mut T, Host: Host + Send>,
            >(
                linker: &mut wasmtime::component::Linker<T>,
                host_getter: G,
            ) -> wasmtime::Result<()>
            where
                T: Send + 'static,
            {
                let mut inst = linker.instance("foo:foo/floats")?;
                inst.func_wrap_concurrent(
                    "f32-param",
                    move |mut caller: wasmtime::StoreContextMut<'_, T>, (arg0,): (f32,)| {
                        _ = host_getter;
                        let mut accessor = unsafe {
                            wasmtime::component::Accessor::new(
                                caller.inner(),
                                || HOST.with(|v| v.get()).cast(),
                                |future| SPAWNED.with(|v| v.borrow_mut().push(future)),
                            )
                        };
                        let mut future = wasmtime::component::__internal::Box::pin(async move {
                            let r = <G::Host as Host>::f32_param(&mut accessor, arg0)
                                .await;
                            Ok(r)
                        });
                        let store = wasmtime::VMStoreRawPtr(caller.traitobj());
                        wasmtime::component::__internal::Box::pin(
                            wasmtime::component::__internal::poll_fn(move |cx| poll(
                                host_getter,
                                store,
                                cx,
                                future.as_mut(),
                            )),
                        )
                    },
                )?;
                inst.func_wrap_concurrent(
                    "f64-param",
                    move |mut caller: wasmtime::StoreContextMut<'_, T>, (arg0,): (f64,)| {
                        _ = host_getter;
                        let mut accessor = unsafe {
                            wasmtime::component::Accessor::new(
                                caller.inner(),
                                || HOST.with(|v| v.get()).cast(),
                                |future| SPAWNED.with(|v| v.borrow_mut().push(future)),
                            )
                        };
                        let mut future = wasmtime::component::__internal::Box::pin(async move {
                            let r = <G::Host as Host>::f64_param(&mut accessor, arg0)
                                .await;
                            Ok(r)
                        });
                        let store = wasmtime::VMStoreRawPtr(caller.traitobj());
                        wasmtime::component::__internal::Box::pin(
                            wasmtime::component::__internal::poll_fn(move |cx| poll(
                                host_getter,
                                store,
                                cx,
                                future.as_mut(),
                            )),
                        )
                    },
                )?;
                inst.func_wrap_concurrent(
                    "f32-result",
                    move |mut caller: wasmtime::StoreContextMut<'_, T>, (): ()| {
                        _ = host_getter;
                        let mut accessor = unsafe {
                            wasmtime::component::Accessor::new(
                                caller.inner(),
                                || HOST.with(|v| v.get()).cast(),
                                |future| SPAWNED.with(|v| v.borrow_mut().push(future)),
                            )
                        };
                        let mut future = wasmtime::component::__internal::Box::pin(async move {
                            let r = <G::Host as Host>::f32_result(&mut accessor).await;
                            Ok((r,))
                        });
                        let store = wasmtime::VMStoreRawPtr(caller.traitobj());
                        wasmtime::component::__internal::Box::pin(
                            wasmtime::component::__internal::poll_fn(move |cx| poll(
                                host_getter,
                                store,
                                cx,
                                future.as_mut(),
                            )),
                        )
                    },
                )?;
                inst.func_wrap_concurrent(
                    "f64-result",
                    move |mut caller: wasmtime::StoreContextMut<'_, T>, (): ()| {
                        _ = host_getter;
                        let mut accessor = unsafe {
                            wasmtime::component::Accessor::new(
                                caller.inner(),
                                || HOST.with(|v| v.get()).cast(),
                                |future| SPAWNED.with(|v| v.borrow_mut().push(future)),
                            )
                        };
                        let mut future = wasmtime::component::__internal::Box::pin(async move {
                            let r = <G::Host as Host>::f64_result(&mut accessor).await;
                            Ok((r,))
                        });
                        let store = wasmtime::VMStoreRawPtr(caller.traitobj());
                        wasmtime::component::__internal::Box::pin(
                            wasmtime::component::__internal::poll_fn(move |cx| poll(
                                host_getter,
                                store,
                                cx,
                                future.as_mut(),
                            )),
                        )
                    },
                )?;
                Ok(())
            }
        }
    }
}
pub mod exports {
    pub mod foo {
        pub mod foo {
            #[allow(clippy::all)]
            pub mod floats {
                #[allow(unused_imports)]
                use wasmtime::component::__internal::{anyhow, Box};
                pub struct Guest {
                    f32_param: wasmtime::component::Func,
                    f64_param: wasmtime::component::Func,
                    f32_result: wasmtime::component::Func,
                    f64_result: wasmtime::component::Func,
                }
                #[derive(Clone)]
                pub struct GuestIndices {
                    f32_param: wasmtime::component::ComponentExportIndex,
                    f64_param: wasmtime::component::ComponentExportIndex,
                    f32_result: wasmtime::component::ComponentExportIndex,
                    f64_result: wasmtime::component::ComponentExportIndex,
                }
                impl GuestIndices {
                    /// Constructor for [`GuestIndices`] which takes a
                    /// [`Component`](wasmtime::component::Component) as input and can be executed
                    /// before instantiation.
                    ///
                    /// This constructor can be used to front-load string lookups to find exports
                    /// within a component.
                    pub fn new(
                        component: &wasmtime::component::Component,
                    ) -> wasmtime::Result<GuestIndices> {
                        let (_, instance) = component
                            .export_index(None, "foo:foo/floats")
                            .ok_or_else(|| {
                                anyhow::anyhow!(
                                    "no exported instance named `foo:foo/floats`"
                                )
                            })?;
                        Self::_new(|name| {
                            component.export_index(Some(&instance), name).map(|p| p.1)
                        })
                    }
                    /// This constructor is similar to [`GuestIndices::new`] except that it
                    /// performs string lookups after instantiation time.
                    pub fn new_instance(
                        mut store: impl wasmtime::AsContextMut,
                        instance: &wasmtime::component::Instance,
                    ) -> wasmtime::Result<GuestIndices> {
                        let instance_export = instance
                            .get_export(&mut store, None, "foo:foo/floats")
                            .ok_or_else(|| {
                                anyhow::anyhow!(
                                    "no exported instance named `foo:foo/floats`"
                                )
                            })?;
                        Self::_new(|name| {
                            instance.get_export(&mut store, Some(&instance_export), name)
                        })
                    }
                    fn _new(
                        mut lookup: impl FnMut(
                            &str,
                        ) -> Option<wasmtime::component::ComponentExportIndex>,
                    ) -> wasmtime::Result<GuestIndices> {
                        let mut lookup = move |name| {
                            lookup(name)
                                .ok_or_else(|| {
                                    anyhow::anyhow!(
                                        "instance export `foo:foo/floats` does \
                not have export `{name}`"
                                    )
                                })
                        };
                        let _ = &mut lookup;
                        let f32_param = lookup("f32-param")?;
                        let f64_param = lookup("f64-param")?;
                        let f32_result = lookup("f32-result")?;
                        let f64_result = lookup("f64-result")?;
                        Ok(GuestIndices {
                            f32_param,
                            f64_param,
                            f32_result,
                            f64_result,
                        })
                    }
                    pub fn load(
                        &self,
                        mut store: impl wasmtime::AsContextMut,
                        instance: &wasmtime::component::Instance,
                    ) -> wasmtime::Result<Guest> {
                        let mut store = store.as_context_mut();
                        let _ = &mut store;
                        let _instance = instance;
                        let f32_param = *_instance
                            .get_typed_func::<(f32,), ()>(&mut store, &self.f32_param)?
                            .func();
                        let f64_param = *_instance
                            .get_typed_func::<(f64,), ()>(&mut store, &self.f64_param)?
                            .func();
                        let f32_result = *_instance
                            .get_typed_func::<(), (f32,)>(&mut store, &self.f32_result)?
                            .func();
                        let f64_result = *_instance
                            .get_typed_func::<(), (f64,)>(&mut store, &self.f64_result)?
                            .func();
                        Ok(Guest {
                            f32_param,
                            f64_param,
                            f32_result,
                            f64_result,
                        })
                    }
                }
                impl Guest {
                    pub async fn call_f32_param<S: wasmtime::AsContextMut>(
                        &self,
                        mut store: S,
                        arg0: f32,
                    ) -> wasmtime::Result<wasmtime::component::Promise<()>>
                    where
                        <S as wasmtime::AsContext>::Data: Send,
                    {
                        let callee = unsafe {
                            wasmtime::component::TypedFunc::<
                                (f32,),
                                (),
                            >::new_unchecked(self.f32_param)
                        };
                        let promise = callee
                            .call_concurrent(store.as_context_mut(), (arg0,))
                            .await?;
                        Ok(promise)
                    }
                    pub async fn call_f64_param<S: wasmtime::AsContextMut>(
                        &self,
                        mut store: S,
                        arg0: f64,
                    ) -> wasmtime::Result<wasmtime::component::Promise<()>>
                    where
                        <S as wasmtime::AsContext>::Data: Send,
                    {
                        let callee = unsafe {
                            wasmtime::component::TypedFunc::<
                                (f64,),
                                (),
                            >::new_unchecked(self.f64_param)
                        };
                        let promise = callee
                            .call_concurrent(store.as_context_mut(), (arg0,))
                            .await?;
                        Ok(promise)
                    }
                    pub async fn call_f32_result<S: wasmtime::AsContextMut>(
                        &self,
                        mut store: S,
                    ) -> wasmtime::Result<wasmtime::component::Promise<f32>>
                    where
                        <S as wasmtime::AsContext>::Data: Send,
                    {
                        let callee = unsafe {
                            wasmtime::component::TypedFunc::<
                                (),
                                (f32,),
                            >::new_unchecked(self.f32_result)
                        };
                        let promise = callee
                            .call_concurrent(store.as_context_mut(), ())
                            .await?;
                        Ok(promise.map(|(v,)| v))
                    }
                    pub async fn call_f64_result<S: wasmtime::AsContextMut>(
                        &self,
                        mut store: S,
                    ) -> wasmtime::Result<wasmtime::component::Promise<f64>>
                    where
                        <S as wasmtime::AsContext>::Data: Send,
                    {
                        let callee = unsafe {
                            wasmtime::component::TypedFunc::<
                                (),
                                (f64,),
                            >::new_unchecked(self.f64_result)
                        };
                        let promise = callee
                            .call_concurrent(store.as_context_mut(), ())
                            .await?;
                        Ok(promise.map(|(v,)| v))
                    }
                }
            }
        }
    }
}
