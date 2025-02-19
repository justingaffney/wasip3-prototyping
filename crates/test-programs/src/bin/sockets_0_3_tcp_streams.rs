use core::future::Future;

use futures::{join, SinkExt as _, StreamExt as _, TryStreamExt as _};
use test_programs::p3::wasi::sockets::types::{
    ErrorCode, IpAddress, IpAddressFamily, IpSocketAddress, TcpSocket,
};
use test_programs::p3::wit_stream;

struct Component;

test_programs::p3::export!(Component);

impl test_programs::p3::exports::wasi::cli::run::Guest for Component {
    async fn run() -> Result<(), ()> {
        test_tcp_input_stream_should_be_closed_by_remote_shutdown(IpAddressFamily::Ipv4).await;
        test_tcp_input_stream_should_be_closed_by_remote_shutdown(IpAddressFamily::Ipv6).await;

        test_tcp_input_stream_should_be_closed_by_local_shutdown(IpAddressFamily::Ipv4).await;
        test_tcp_input_stream_should_be_closed_by_local_shutdown(IpAddressFamily::Ipv6).await;

        test_tcp_output_stream_should_be_closed_by_local_shutdown(IpAddressFamily::Ipv4).await;
        test_tcp_output_stream_should_be_closed_by_local_shutdown(IpAddressFamily::Ipv6).await;

        test_tcp_shutdown_should_not_lose_data(IpAddressFamily::Ipv4).await;
        test_tcp_shutdown_should_not_lose_data(IpAddressFamily::Ipv6).await;
        Ok(())
    }
}

/// InputStream::read should return `StreamError::Closed` after the connection has been shut down by the server.
async fn test_tcp_input_stream_should_be_closed_by_remote_shutdown(family: IpAddressFamily) {
    setup(family, |server, client| async move {
        let (mut server_tx, server_rx) = wit_stream::new();
        join!(
            async {
                server.send(server_rx).await.unwrap();
            },
            async {
                // Shut down the connection from the server side:
                server_tx.close().await.unwrap();
                drop(server_tx);
            },
        );
        drop(server);

        let (mut client_rx, client_fut) = client.receive();

        // The input stream should immediately signal StreamError::Closed.
        // Notably, it should _not_ return an empty list (the wasi-io equivalent of EWOULDBLOCK)
        // See: https://github.com/bytecodealliance/wasmtime/pull/8968

        // TODO: Verify

        // Wait for the shutdown signal to reach the client:
        assert!(client_rx.next().await.is_none());
        assert_eq!(client_fut.await, Some(Ok(Err(ErrorCode::ConnectionReset))));
    })
    .await;
}

/// InputStream::read should return `StreamError::Closed` after the connection has been shut down locally.
async fn test_tcp_input_stream_should_be_closed_by_local_shutdown(family: IpAddressFamily) {
    setup(family, |server, client| async move {
        let (mut server_tx, server_rx) = wit_stream::new();
        join!(
            async {
                server.send(server_rx).await.unwrap();
            },
            async {
                // On Linux, `recv` continues to work even after `shutdown(sock, SHUT_RD)`
                // has been called. To properly test that this behavior doesn't happen in
                // WASI, we make sure there's some data to read by the client:
                server_tx.send(b"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.".into()).await.unwrap();
                drop(server_tx);
            },
    );

        let (client_rx, client_fut) = client.receive();

        // TODO: Verify

        // Shut down socket locally:
        drop(client_rx);
        // Wait for the shutdown signal to reach the client:
        assert_eq!(client_fut.await, Some(Ok(Err(ErrorCode::ConnectionReset))));
    }).await;
}

/// OutputStream should return `StreamError::Closed` after the connection has been locally shut down for sending.
async fn test_tcp_output_stream_should_be_closed_by_local_shutdown(family: IpAddressFamily) {
    setup(family, |server, client| async move {
        let (server_tx, server_rx) = wit_stream::new();
        drop(server_tx);
        server.send(server_rx).await.unwrap();

        let (server_tx, server_rx) = wit_stream::new();
        drop(server_tx);
        assert_eq!(
            server.send(server_rx).await,
            Err(ErrorCode::ConnectionReset)
        );

        let (client_tx, client_rx) = wit_stream::new();
        drop(client_tx);
        client.send(client_rx).await.unwrap();

        let (client_tx, client_rx) = wit_stream::new();
        drop(client_tx);
        assert_eq!(
            client.send(client_rx).await,
            Err(ErrorCode::ConnectionReset)
        );
    })
    .await;
}

/// Calling `shutdown` while the OutputStream is in the middle of a background write should not cause that write to be lost.
async fn test_tcp_shutdown_should_not_lose_data(family: IpAddressFamily) {
    setup(family, |server, client| async move {
        // Minimize the local send buffer:
        client.set_send_buffer_size(1024).unwrap();
        let small_buffer_size = client.send_buffer_size().unwrap();

        // Create a significantly bigger buffer, so that we can be pretty sure the `write` won't finish immediately:
        let big_buffer_size = 100 * small_buffer_size;
        assert!(big_buffer_size > small_buffer_size);
        let outgoing_data = vec![0; big_buffer_size as usize];

        // Submit the oversized buffer and immediately initiate the shutdown:
        let (mut client_tx, client_rx) = wit_stream::new();
        join!(
            async {
                client.send(client_rx).await.unwrap();
            },
            async {
                client_tx.send(outgoing_data.clone()).await.unwrap();
                client_tx.close().await.unwrap();
                drop(client_tx);
            },
        );

        // The peer should receive _all_ data:
        let (server_rx, server_fut) = server.receive();
        let incoming_data = server_rx.try_collect::<Vec<_>>().await.unwrap().concat();
        assert_eq!(
            outgoing_data.len(),
            incoming_data.len(),
            "Received data should match the sent data"
        );
        server_fut.await.unwrap().unwrap().unwrap()
    })
    .await;
}

fn main() {}

/// Set up a connected pair of sockets
async fn setup<Fut: Future<Output = ()>>(
    family: IpAddressFamily,
    body: impl FnOnce(TcpSocket, TcpSocket) -> Fut,
) {
    let bind_address = IpSocketAddress::new(IpAddress::new_loopback(family), 0);
    let listener = TcpSocket::new(family);
    listener.bind(bind_address).unwrap();
    let mut accept = listener.listen().unwrap();
    let bound_address = listener.local_address().unwrap();
    let client_socket = TcpSocket::new(family);
    client_socket.connect(bound_address).await.unwrap();
    let mut accepted_socket = accept.next().await.unwrap().unwrap();
    assert_eq!(accepted_socket.len(), 1);
    let accepted_socket = accepted_socket.pop().unwrap();

    body(accepted_socket, client_socket).await;
}
