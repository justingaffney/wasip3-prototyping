use core::future::{poll_fn, Future};
use core::mem;
use core::net::SocketAddr;
use core::pin::{pin, Pin};
use core::task::Poll;

use std::net::Shutdown;
use std::sync::Arc;

use anyhow::{ensure, Context as _};
use io_lifetimes::AsSocketlike as _;
use rustix::io::Errno;
use tokio::sync::{mpsc, oneshot};
use wasmtime::component::{
    future, stream, Accessor, BackgroundTask, FutureReader, FutureWriter, Lift, Resource,
    ResourceTable, StreamReader, StreamWriter,
};

use crate::p3::bindings::sockets::types::{
    Duration, ErrorCode, HostTcpSocket, IpAddressFamily, IpSocketAddress, TcpSocket,
};
use crate::p3::sockets::tcp::{bind, TcpState};
use crate::p3::sockets::util::is_valid_unicast_address;
use crate::p3::sockets::{SocketAddrUse, SocketAddressFamily, WasiSocketsImpl, WasiSocketsView};
use crate::runtime::spawn;

fn is_tcp_allowed<T>(store: &mut Accessor<T>) -> bool
where
    T: WasiSocketsView,
{
    store.with(|store| store.data().sockets().allowed_network_uses.tcp)
}

async fn is_addr_allowed<T>(
    store: &mut Accessor<T>,
    addr: SocketAddr,
    reason: SocketAddrUse,
) -> bool
where
    T: WasiSocketsView,
{
    store
        .with(|store| {
            let socket_addr_check = store.data().sockets().socket_addr_check.clone();
            async move { socket_addr_check(addr, reason).await }
        })
        .await
}

fn get_socket<'a>(
    table: &'a ResourceTable,
    socket: &'a Resource<TcpSocket>,
) -> wasmtime::Result<&'a TcpSocket> {
    table
        .get(socket)
        .context("failed to get socket resource from table")
}

fn get_socket_mut<'a>(
    table: &'a mut ResourceTable,
    socket: &'a Resource<TcpSocket>,
) -> wasmtime::Result<&'a mut TcpSocket> {
    table
        .get_mut(socket)
        .context("failed to get socket resource from table")
}

fn next_item<T, U>(
    store: &mut Accessor<T>,
    stream: StreamReader<U>,
) -> wasmtime::Result<
    Pin<Box<dyn Future<Output = Option<(StreamReader<U>, Vec<U>)>> + Send + Sync + 'static>>,
>
where
    U: Send + Sync + Lift + 'static,
{
    let fut = store.with(|mut store| stream.read(&mut store).context("failed to read stream"))?;
    Ok(fut.into_future())
}

struct BackgroundTaskFn<T>(T);

impl<T, F, Fut> BackgroundTask<T> for BackgroundTaskFn<F>
where
    F: FnOnce(&mut Accessor<T>) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = wasmtime::Result<()>> + Send + Sync,
{
    fn run(
        self,
        accessor: &mut Accessor<T>,
    ) -> impl Future<Output = wasmtime::Result<()>> + Send + Sync {
        self.0(accessor)
    }
}

struct ListenTask {
    family: SocketAddressFamily,
    tx: StreamWriter<Resource<TcpSocket>>,
    rx: mpsc::Receiver<std::io::Result<(tokio::net::TcpStream, SocketAddr)>>,

    // The socket options below are not automatically inherited from the listener
    // on all platforms. So we keep track of which options have been explicitly
    // set and manually apply those values to newly accepted clients.
    #[cfg(target_os = "macos")]
    receive_buffer_size: Arc<core::sync::atomic::AtomicUsize>,
    #[cfg(target_os = "macos")]
    send_buffer_size: Arc<core::sync::atomic::AtomicUsize>,
    #[cfg(target_os = "macos")]
    hop_limit: Arc<core::sync::atomic::AtomicU8>,
    #[cfg(target_os = "macos")]
    keep_alive_idle_time: Arc<core::sync::atomic::AtomicU64>, // nanoseconds
}

impl<T: WasiSocketsView> BackgroundTask<T> for ListenTask {
    async fn run(mut self, store: &mut Accessor<T>) -> wasmtime::Result<()> {
        let mut tx = self.tx;
        while let Some(res) = self.rx.recv().await {
            let state = match res {
                Ok((stream, _addr)) => {
                    #[cfg(target_os = "macos")]
                    {
                        // Manually inherit socket options from listener. We only have to
                        // do this on platforms that don't already do this automatically
                        // and only if a specific value was explicitly set on the listener.

                        let receive_buffer_size = self
                            .receive_buffer_size
                            .load(core::sync::atomic::Ordering::Relaxed);
                        if receive_buffer_size > 0 {
                            // Ignore potential error.
                            _ = rustix::net::sockopt::set_socket_recv_buffer_size(
                                &stream,
                                receive_buffer_size,
                            );
                        }

                        let send_buffer_size = self
                            .send_buffer_size
                            .load(core::sync::atomic::Ordering::Relaxed);
                        if send_buffer_size > 0 {
                            // Ignore potential error.
                            _ = rustix::net::sockopt::set_socket_send_buffer_size(
                                &stream,
                                send_buffer_size,
                            );
                        }

                        // For some reason, IP_TTL is inherited, but IPV6_UNICAST_HOPS isn't.
                        if self.family == SocketAddressFamily::Ipv6 {
                            let hop_limit =
                                self.hop_limit.load(core::sync::atomic::Ordering::Relaxed);
                            if hop_limit > 0 {
                                // Ignore potential error.
                                _ = rustix::net::sockopt::set_ipv6_unicast_hops(
                                    &stream,
                                    Some(hop_limit),
                                );
                            }
                        }

                        let keep_alive_idle_time = self
                            .keep_alive_idle_time
                            .load(core::sync::atomic::Ordering::Relaxed);
                        if keep_alive_idle_time > 0 {
                            // Ignore potential error.
                            _ = rustix::net::sockopt::set_tcp_keepidle(
                                &stream,
                                core::time::Duration::from_nanos(keep_alive_idle_time),
                            );
                        }
                    }
                    TcpState::Connected {
                        stream: Arc::new(stream),
                        abort_receive: None,
                    }
                }
                Err(err) => {
                    match Errno::from_io_error(&err) {
                        // From: https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-accept#:~:text=WSAEINPROGRESS
                        // > WSAEINPROGRESS: A blocking Windows Sockets 1.1 call is in progress,
                        // > or the service provider is still processing a callback function.
                        //
                        // wasi-sockets doesn't have an equivalent to the EINPROGRESS error,
                        // because in POSIX this error is only returned by a non-blocking
                        // `connect` and wasi-sockets has a different solution for that.
                        #[cfg(windows)]
                        Some(Errno::INPROGRESS) => TcpState::Error(ErrorCode::Unknown),

                        // Normalize Linux' non-standard behavior.
                        //
                        // From https://man7.org/linux/man-pages/man2/accept.2.html:
                        // > Linux accept() passes already-pending network errors on the
                        // > new socket as an error code from accept(). This behavior
                        // > differs from other BSD socket implementations. (...)
                        #[cfg(target_os = "linux")]
                        Some(
                            Errno::CONNRESET
                            | Errno::NETRESET
                            | Errno::HOSTUNREACH
                            | Errno::HOSTDOWN
                            | Errno::NETDOWN
                            | Errno::NETUNREACH
                            | Errno::PROTO
                            | Errno::NOPROTOOPT
                            | Errno::NONET
                            | Errno::OPNOTSUPP,
                        ) => TcpState::Error(ErrorCode::ConnectionAborted),
                        _ => TcpState::Error(err.into()),
                    }
                }
            };
            let fut = store.with(|mut store| {
                let socket = store
                    .data_mut()
                    .table()
                    .push(TcpSocket::from_state(state, self.family))
                    .context("failed to push socket to table")?;
                tx.write(store, vec![socket])
                    .context("failed to send socket")
            })?;
            tx = fut.into_future().await;
        }
        Ok(())
    }
}

struct ReceiveTask {
    stream: Arc<tokio::net::TcpStream>,
    data: StreamWriter<u8>,
    result: FutureWriter<Result<(), ErrorCode>>,
    abort: oneshot::Receiver<()>,
}

impl<T: WasiSocketsView> BackgroundTask<T> for ReceiveTask {
    async fn run(self, store: &mut Accessor<T>) -> wasmtime::Result<()> {
        let mut abort = pin!(self.abort);
        let mut tx = self.data;
        let res = loop {
            let mut buf = vec![0; 8096];
            match self.stream.try_read(&mut buf) {
                Ok(0) => {
                    if let Err(err) = self
                        .stream
                        .as_socketlike_view::<std::net::TcpStream>()
                        .shutdown(Shutdown::Read)
                    {
                        break Err(err.into());
                    }
                }
                Ok(n) => {
                    buf.truncate(n);
                    let fut =
                        store.with(|store| tx.write(store, buf).context("failed to send chunk"))?;
                    let mut fut = fut.into_future();
                    tx = match poll_fn(|cx| match abort.as_mut().poll(cx) {
                        Poll::Ready(..) => Poll::Ready(None),
                        Poll::Pending => fut.as_mut().poll(cx).map(Some),
                    })
                    .await
                    {
                        Some(tx) => tx,
                        None => {
                            // socket dropped, abort
                            break Ok(());
                        }
                    };
                }
                Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => {
                    let mut writable = pin!(self.stream.writable());
                    match poll_fn(|cx| match abort.as_mut().poll(cx) {
                        Poll::Ready(..) => Poll::Ready(None),
                        Poll::Pending => writable.as_mut().poll(cx).map(Some),
                    })
                    .await
                    {
                        Some(Ok(())) => {}
                        Some(Err(err)) => break Err(err.into()),
                        None => {
                            // socket dropped, abort
                            break Ok(());
                        }
                    }
                }
                Err(err) => break Err(err.into()),
            }
        };
        let fut = store.with(|store| {
            self.result
                .write(store, res)
                .context("failed to write result")
        })?;
        let mut fut = fut.into_future();
        poll_fn(|cx| match abort.as_mut().poll(cx) {
            Poll::Ready(..) => Poll::Ready(()),
            Poll::Pending => fut.as_mut().poll(cx),
        })
        .await;
        Ok(())
    }
}

impl<T> HostTcpSocket for WasiSocketsImpl<&mut T>
where
    T: WasiSocketsView + 'static,
{
    type TcpSocketData = T;

    fn new(&mut self, address_family: IpAddressFamily) -> wasmtime::Result<Resource<TcpSocket>> {
        let socket = TcpSocket::new(address_family.into()).context("failed to create socket")?;
        let socket = self
            .table()
            .push(socket)
            .context("failed to push socket resource to table")?;
        Ok(socket)
    }

    async fn bind(
        store: &mut Accessor<Self::TcpSocketData>,
        socket: Resource<TcpSocket>,
        local_address: IpSocketAddress,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let local_address = SocketAddr::from(local_address);
        if !is_tcp_allowed(store)
            || !is_addr_allowed(store, local_address, SocketAddrUse::TcpBind).await
        {
            return Ok(Err(ErrorCode::AccessDenied));
        }
        store.with(|mut store| {
            let socket = get_socket_mut(store.data_mut().table(), &socket)?;
            if !is_valid_unicast_address(local_address.ip(), socket.family) {
                return Ok(Err(ErrorCode::InvalidArgument));
            }
            match mem::replace(&mut socket.tcp_state, TcpState::Closed) {
                TcpState::Default(sock) => {
                    if let Err(err) = bind(&sock, local_address) {
                        socket.tcp_state = TcpState::Default(sock);
                        Ok(Err(err))
                    } else {
                        socket.tcp_state = TcpState::Bound(sock);
                        Ok(Ok(()))
                    }
                }
                tcp_state => {
                    socket.tcp_state = tcp_state;
                    Ok(Err(ErrorCode::InvalidState))
                }
            }
        })
    }

    async fn connect(
        store: &mut Accessor<Self::TcpSocketData>,
        socket: Resource<TcpSocket>,
        remote_address: IpSocketAddress,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let remote_address = SocketAddr::from(remote_address);
        if !is_tcp_allowed(store)
            || !is_addr_allowed(store, remote_address, SocketAddrUse::TcpConnect).await
        {
            return Ok(Err(ErrorCode::AccessDenied));
        }
        let ip = remote_address.ip().to_canonical();
        if ip.is_unspecified() || remote_address.port() == 0 {
            return Ok(Err(ErrorCode::InvalidArgument));
        }

        match store.with(|mut store| {
            let socket = get_socket_mut(store.data_mut().table(), &socket)?;
            if !is_valid_unicast_address(ip, socket.family) {
                return Ok(Err(ErrorCode::InvalidArgument));
            }
            match mem::replace(&mut socket.tcp_state, TcpState::Connecting) {
                TcpState::Default(sock) | TcpState::Bound(sock) => Ok(Ok(sock)),
                tcp_state => {
                    socket.tcp_state = tcp_state;
                    Ok(Err(ErrorCode::InvalidState))
                }
            }
        }) {
            Ok(Ok(sock)) => {
                let res = sock.connect(remote_address).await;
                store.with(|mut store| {
                    let socket = get_socket_mut(store.data_mut().table(), &socket)?;
                    ensure!(
                        matches!(socket.tcp_state, TcpState::Connecting),
                        "corrupted socket state"
                    );
                    match res {
                        Ok(stream) => {
                            socket.tcp_state = TcpState::Connected {
                                stream: Arc::new(stream),
                                abort_receive: None,
                            };
                            Ok(Ok(()))
                        }
                        Err(err) => {
                            socket.tcp_state = TcpState::Closed;
                            Ok(Err(err.into()))
                        }
                    }
                })
            }
            Ok(Err(err)) => Ok(Err(err)),
            Err(err) => Err(err),
        }
    }

    async fn listen(
        store: &mut Accessor<Self::TcpSocketData>,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<StreamReader<Resource<TcpSocket>>, ErrorCode>> {
        match store.with(|mut store| {
            let data = store.data_mut();
            if !data.sockets().allowed_network_uses.tcp {
                return Ok(Err(ErrorCode::AccessDenied));
            }
            let sock = {
                let socket = get_socket_mut(data.table(), &socket)?;
                match mem::replace(&mut socket.tcp_state, TcpState::Closed) {
                    TcpState::Default(sock) | TcpState::Bound(sock) => sock,
                    tcp_state => {
                        socket.tcp_state = tcp_state;
                        return Ok(Err(ErrorCode::InvalidState));
                    }
                }
            };
            let (tx, rx) = stream(&mut store).context("failed to create stream")?;
            let &TcpSocket {
                listen_backlog_size,
                ..
            } = get_socket(store.data_mut().table(), &socket)?;

            match sock.listen(listen_backlog_size) {
                Ok(listener) => {
                    let listener = Arc::new(listener);
                    let TcpSocket {
                        tcp_state,
                        family,
                        #[cfg(target_os = "macos")]
                        receive_buffer_size,
                        #[cfg(target_os = "macos")]
                        send_buffer_size,
                        #[cfg(target_os = "macos")]
                        hop_limit,
                        #[cfg(target_os = "macos")]
                        keep_alive_idle_time,
                        ..
                    } = get_socket_mut(store.data_mut().table(), &socket)?;
                    let (task_tx, task_rx) = mpsc::channel(1);
                    let (finished_tx, finished_rx) = std::sync::mpsc::channel();
                    let (abort_tx, abort_rx) = oneshot::channel();
                    *tcp_state = TcpState::Listening {
                        listener: Arc::clone(&listener),
                        finished: finished_rx,
                        abort: abort_tx,
                        task: spawn(async move {
                            let mut abort = pin!(abort_rx);
                            loop {
                                let accept = listener.accept();
                                let mut accept = pin!(accept);
                                let Some(res) = poll_fn(|cx| match abort.as_mut().poll(cx) {
                                    Poll::Ready(..) => Poll::Ready(None),
                                    Poll::Pending => accept.as_mut().poll(cx).map(Some),
                                })
                                .await
                                else {
                                    break;
                                };
                                let send = task_tx.send(res);
                                let mut send = pin!(send);
                                match poll_fn(|cx| match abort.as_mut().poll(cx) {
                                    Poll::Ready(..) => Poll::Ready(None),
                                    Poll::Pending => send.as_mut().poll(cx).map(Some),
                                })
                                .await
                                {
                                    None | Some(Err(..)) => break,
                                    Some(Ok(())) => {}
                                }
                            }
                            drop(listener);
                            _ = finished_tx.send(());
                        }),
                    };
                    Ok(Ok((
                        rx,
                        ListenTask {
                            family: *family,
                            tx,
                            rx: task_rx,
                            #[cfg(target_os = "macos")]
                            receive_buffer_size: Arc::clone(&receive_buffer_size),
                            #[cfg(target_os = "macos")]
                            send_buffer_size: Arc::clone(&send_buffer_size),
                            #[cfg(target_os = "macos")]
                            hop_limit: Arc::clone(&hop_limit),
                            #[cfg(target_os = "macos")]
                            keep_alive_idle_time: Arc::clone(&keep_alive_idle_time),
                        },
                    )))
                }
                Err(err) => {
                    match Errno::from_io_error(&err) {
                        // See: https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-listen#:~:text=WSAEMFILE
                        // According to the docs, `listen` can return EMFILE on Windows.
                        // This is odd, because we're not trying to create a new socket
                        // or file descriptor of any kind. So we rewrite it to less
                        // surprising error code.
                        //
                        // At the time of writing, this behavior has never been experimentally
                        // observed by any of the wasmtime authors, so we're relying fully
                        // on Microsoft's documentation here.
                        #[cfg(windows)]
                        Some(Errno::MFILE) => Ok(Err(ErrorCode::OutOfMemory)),

                        _ => Ok(Err(err.into())),
                    }
                }
            }
        }) {
            Ok(Ok((rx, task))) => {
                store.spawn(task);
                Ok(Ok(rx))
            }
            Ok(Err(err)) => Ok(Err(err)),
            Err(err) => Err(err),
        }
    }

    async fn send(
        store: &mut Accessor<Self::TcpSocketData>,
        socket: Resource<TcpSocket>,
        data: StreamReader<u8>,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let (stream, fut) = match store.with(|mut store| {
            let fut = data.read(&mut store).context("failed to get data stream")?;
            let sock = get_socket(store.data_mut().table(), &socket)?;
            if let TcpState::Connected { stream, .. } = &sock.tcp_state {
                Ok(Ok((Arc::clone(&stream), fut)))
            } else {
                Ok(Err(ErrorCode::InvalidState))
            }
        }) {
            Ok(Ok((stream, fut))) => (stream, fut),
            Ok(Err(err)) => return Ok(Err(err)),
            Err(err) => return Err(err),
        };
        let mut fut = fut.into_future();
        'outer: loop {
            let Some((tail, mut buf)) = fut.await else {
                match stream
                    .as_socketlike_view::<std::net::TcpStream>()
                    .shutdown(Shutdown::Write)
                {
                    Ok(()) => return Ok(Ok(())),
                    Err(err) => return Ok(Err(err.into())),
                }
            };
            let mut buf = buf.as_mut_slice();
            loop {
                match stream.try_write(&buf) {
                    Ok(n) => {
                        if n == buf.len() {
                            fut = next_item(store, tail)?;
                            continue 'outer;
                        } else {
                            buf = &mut buf[n..];
                        }
                    }
                    Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => {
                        if let Err(err) = stream.writable().await {
                            return Ok(Err(err.into()));
                        }
                    }
                    Err(err) => return Ok(Err(err.into())),
                }
            }
        }
    }

    async fn receive(
        store: &mut Accessor<Self::TcpSocketData>,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<(StreamReader<u8>, FutureReader<Result<(), ErrorCode>>)> {
        store.with(|mut store| {
            let (data_tx, data_rx) = stream(&mut store).context("failed to create stream")?;
            let (res_tx, res_rx) = future(&mut store).context("failed to create future")?;
            let sock = get_socket_mut(store.data_mut().table(), &socket)?;
            let (abort_tx, abort_rx) = oneshot::channel();
            if let TcpState::Connected {
                stream,
                abort_receive,
            } = &mut sock.tcp_state
            {
                ensure!(
                    abort_receive.replace(abort_tx).is_none(),
                    "`receive` can called at most once"
                );
                let stream = Arc::clone(&stream);
                store.spawn(ReceiveTask {
                    stream,
                    data: data_tx,
                    result: res_tx,
                    abort: abort_rx,
                });
            } else {
                let fut = res_tx
                    .write(&mut store, Err(ErrorCode::InvalidState))
                    .context("failed to write result to future")?;
                let fut = fut.into_future();
                store.spawn(BackgroundTaskFn(
                    |_: &mut Accessor<Self::TcpSocketData>| async {
                        fut.await;
                        Ok(())
                    },
                ));
            }
            Ok((data_rx, res_rx))
        })
    }

    fn local_address(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<IpSocketAddress, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.local_address())
    }

    fn remote_address(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<IpSocketAddress, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.remote_address())
    }

    fn is_listening(&mut self, socket: Resource<TcpSocket>) -> wasmtime::Result<bool> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.is_listening())
    }

    fn address_family(&mut self, socket: Resource<TcpSocket>) -> wasmtime::Result<IpAddressFamily> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.address_family())
    }

    fn set_listen_backlog_size(
        &mut self,
        socket: Resource<TcpSocket>,
        value: u64,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket_mut(self.table(), &socket)?;
        Ok(sock.set_listen_backlog_size(value))
    }

    fn keep_alive_enabled(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<bool, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.keep_alive_enabled())
    }

    fn set_keep_alive_enabled(
        &mut self,
        socket: Resource<TcpSocket>,
        value: bool,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.set_keep_alive_enabled(value))
    }

    fn keep_alive_idle_time(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<Duration, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.keep_alive_idle_time())
    }

    fn set_keep_alive_idle_time(
        &mut self,
        socket: Resource<TcpSocket>,
        value: Duration,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket_mut(self.table(), &socket)?;
        Ok(sock.set_keep_alive_idle_time(value))
    }

    fn keep_alive_interval(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<Duration, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.keep_alive_interval())
    }

    fn set_keep_alive_interval(
        &mut self,
        socket: Resource<TcpSocket>,
        value: Duration,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.set_keep_alive_interval(value))
    }

    fn keep_alive_count(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<u32, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.keep_alive_count())
    }

    fn set_keep_alive_count(
        &mut self,
        socket: Resource<TcpSocket>,
        value: u32,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.set_keep_alive_count(value))
    }

    fn hop_limit(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<u8, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.hop_limit())
    }

    fn set_hop_limit(
        &mut self,
        socket: Resource<TcpSocket>,
        value: u8,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.set_hop_limit(value))
    }

    fn receive_buffer_size(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<u64, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.receive_buffer_size())
    }

    fn set_receive_buffer_size(
        &mut self,
        socket: Resource<TcpSocket>,
        value: u64,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket_mut(self.table(), &socket)?;
        Ok(sock.set_receive_buffer_size(value))
    }

    fn send_buffer_size(
        &mut self,
        socket: Resource<TcpSocket>,
    ) -> wasmtime::Result<Result<u64, ErrorCode>> {
        let sock = get_socket(self.table(), &socket)?;
        Ok(sock.send_buffer_size())
    }

    fn set_send_buffer_size(
        &mut self,
        socket: Resource<TcpSocket>,
        value: u64,
    ) -> wasmtime::Result<Result<(), ErrorCode>> {
        let sock = get_socket_mut(self.table(), &socket)?;
        Ok(sock.set_send_buffer_size(value))
    }

    fn drop(&mut self, rep: Resource<TcpSocket>) -> wasmtime::Result<()> {
        let sock = self
            .table()
            .delete(rep)
            .context("failed to delete socket resource from table")?;
        match sock.tcp_state {
            TcpState::Listening {
                abort,
                finished,
                listener,
                ..
            } => {
                if let Ok(()) = abort.send(()) {
                    // this will unblock only once the task finishes
                    _ = finished.recv();
                }
                // this must be the only reference to the listener left
                ensure!(
                    Arc::into_inner(listener).is_some(),
                    "corrupted listener state"
                );
                Ok(())
            }
            _ => Ok(()),
        }
    }
}
