// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fallible LSP transport and cancellable connection lifetime.

use crate::CleanBackend;
use std::io::{self, Read};
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};
use tokio::sync::mpsc;
use tower_lsp::{ClientSocket, LspService};

mod dispatch;
mod framing;

/// Serve a connection, preserving physical I/O failures and draining committed output.
pub(crate) async fn serve<R, W>(
    reader: R,
    writer: W,
    service: LspService<CleanBackend>,
    socket: ClientSocket,
) -> io::Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite,
{
    dispatch::serve(reader, writer, service, socket).await
}

/// Stdin must not leave an uncancellable blocking read in Tokio's runtime pool.
/// A dedicated OS thread can remain blocked until process exit without delaying
/// runtime destruction. The channel holds at most two queued chunks.
pub(crate) fn stdin() -> io::Result<impl AsyncRead + Unpin> {
    let (sender, receiver) = mpsc::channel(2);
    std::thread::Builder::new()
        .name("clean-lsp-stdin".into())
        .spawn(move || {
            let mut input = io::stdin().lock();
            loop {
                let mut bytes = vec![0; 8192];
                let result = match input.read(&mut bytes) {
                    Ok(0) => break,
                    Ok(count) => {
                        bytes.truncate(count);
                        Ok(bytes)
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => Err(error),
                };
                let failed = result.is_err();
                if sender.blocking_send(result).is_err() || failed {
                    break;
                }
            }
        })?;
    Ok(ChannelReader {
        receiver,
        bytes: Vec::new(),
        offset: 0,
    })
}

struct ChannelReader {
    receiver: mpsc::Receiver<io::Result<Vec<u8>>>,
    bytes: Vec<u8>,
    offset: usize,
}

impl AsyncRead for ChannelReader {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buffer: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let this = self.get_mut();
        if buffer.remaining() == 0 {
            return Poll::Ready(Ok(()));
        }
        while this.offset == this.bytes.len() {
            match this.receiver.poll_recv(cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(None) => return Poll::Ready(Ok(())),
                Poll::Ready(Some(Err(error))) => return Poll::Ready(Err(error)),
                Poll::Ready(Some(Ok(bytes))) => {
                    this.bytes = bytes;
                    this.offset = 0;
                }
            }
        }
        let count = buffer.remaining().min(this.bytes.len() - this.offset);
        buffer.put_slice(&this.bytes[this.offset..this.offset + count]);
        this.offset += count;
        Poll::Ready(Ok(()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};
    use std::time::Duration;
    use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};

    fn frame(message: Value) -> Vec<u8> {
        let body = serde_json::to_vec(&message).expect("encode request");
        let mut bytes = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        bytes.extend(body);
        bytes
    }

    async fn send(writer: &mut (impl AsyncWrite + Unpin), message: Value) {
        writer
            .write_all(&frame(message))
            .await
            .expect("write frame");
    }

    async fn response(reader: &mut BufReader<impl AsyncRead + Unpin>) -> Value {
        let mut length = None;
        loop {
            let mut line = String::new();
            assert_ne!(reader.read_line(&mut line).await.expect("header"), 0);
            if line == "\r\n" {
                break;
            }
            if let Some(value) = line.strip_prefix("Content-Length: ") {
                length = Some(value.trim().parse::<usize>().expect("length"));
            }
        }
        let mut body = vec![0; length.expect("content length")];
        reader.read_exact(&mut body).await.expect("body");
        serde_json::from_slice(&body).expect("response JSON")
    }

    async fn lifecycle(shutdown: Option<Value>, buffered_tail: bool) -> io::Result<()> {
        lifecycle_with_exit(
            shutdown,
            json!({"jsonrpc":"2.0","method":"exit"}),
            buffered_tail,
            false,
        )
        .await
    }

    async fn lifecycle_with_exit(
        shutdown: Option<Value>,
        exit: Value,
        buffered_tail: bool,
        invalid_exit_prefix: bool,
    ) -> io::Result<()> {
        let (client, server) = tokio::io::duplex(16_384);
        let (read, write) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(read, write, service, socket));
        let (read, mut write) = tokio::io::split(client);
        let mut read = BufReader::new(read);
        send(
            &mut write,
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        )
        .await;
        assert!(response(&mut read).await.get("result").is_some());
        if let Some(request) = shutdown {
            send(&mut write, request).await;
            let reply = response(&mut read).await;
            assert_eq!(reply.get("id"), Some(&json!(2)), "{reply}");
            assert_eq!(reply.get("result"), Some(&Value::Null), "{reply}");
            assert!(reply.get("error").is_none(), "{reply}");
            assert!(
                !task.is_finished(),
                "shutdown alone must keep the server alive"
            );
        }
        if invalid_exit_prefix {
            send(
                &mut write,
                json!({"jsonrpc":"2.0","method":"exit","params":{"probe":true}}),
            )
            .await;
            // A reply proves the malformed exit did not advance the inner
            // service to Exited. Hover changes no shutdown authorization.
            send(
                &mut write,
                json!({"jsonrpc":"2.0","id":3,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///exit-barrier.lean"},"position":{"line":0,"character":0}}}),
            )
            .await;
            let reply = tokio::time::timeout(Duration::from_secs(5), response(&mut read))
                .await
                .expect("malformed exit must leave the service able to reply");
            assert_eq!(reply.get("id"), Some(&json!(3)), "{reply}");
            assert_ne!(
                reply.get("result").is_some(),
                reply.get("error").is_some(),
                "{reply}"
            );
            assert!(!task.is_finished(), "malformed exit must keep input open");
        }
        let mut bytes = frame(exit);
        if buffered_tail {
            bytes.extend(frame(
                json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":999}}),
            ));
            bytes.extend(frame(
                json!({"jsonrpc":"2.0","id":999,"method":"textDocument/hover","params":{}}),
            ));
        }
        write
            .write_all(&bytes)
            .await
            .expect("single buffered write");
        // Keep the client's write half open throughout the server's completion.
        let result = tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("exit must wake the transport without another input frame")
            .expect("server task");
        drop(write);
        result
    }

    #[tokio::test]
    async fn accepted_shutdown_then_exit_finishes_with_input_open() {
        lifecycle(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
            false,
        )
        .await
        .expect("orderly exit");
    }

    #[tokio::test]
    async fn exit_with_buffered_tail_finishes_with_input_open() {
        lifecycle(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
            true,
        )
        .await
        .expect("buffered frames after exit must not bypass transport cleanup");
    }

    #[tokio::test]
    async fn accepted_null_shutdown_then_exit_finishes_with_input_open() {
        lifecycle(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null})),
            false,
        )
        .await
        .expect("explicit null shutdown authorizes orderly exit");
    }

    #[tokio::test]
    async fn accepted_null_shutdown_with_buffered_tail_finishes_with_input_open() {
        lifecycle(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null})),
            true,
        )
        .await
        .expect("explicit null shutdown keeps buffered-tail cleanup");
    }

    #[tokio::test]
    async fn exit_without_shutdown_reports_failure_with_input_open() {
        assert!(lifecycle(None, false).await.is_err());
    }

    #[tokio::test]
    async fn structured_shutdown_authorizes_successful_exit() {
        lifecycle(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":{"unexpected":true}})),
            false,
        )
        .await
        .expect("official35/36 accept structured shutdown parameters");
    }

    #[tokio::test]
    async fn null_exit_after_shutdown_finishes_with_input_open() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            false,
        )
        .await
        .expect("null exit after accepted shutdown");
    }

    #[tokio::test]
    async fn null_exit_after_null_shutdown_finishes_with_input_open() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            false,
        )
        .await
        .expect("null shutdown and exit");
    }

    #[tokio::test]
    async fn null_exit_with_buffered_tail_finishes_with_input_open() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            true,
            false,
        )
        .await
        .expect("null exit keeps buffered-tail cleanup");
    }

    #[tokio::test]
    async fn null_exit_after_null_shutdown_with_buffered_tail_finishes_with_input_open() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            true,
            false,
        )
        .await
        .expect("null shutdown and exit keep buffered-tail cleanup");
    }

    #[tokio::test]
    async fn invalid_object_exit_keeps_connection_available_for_null_exit() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            true,
        )
        .await
        .expect("valid null exit still works after a malformed notification");
    }

    #[tokio::test]
    async fn invalid_object_exit_keeps_buffered_null_exit_cleanup() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            true,
            true,
        )
        .await
        .expect("malformed notification preserves later buffered exit cleanup");
    }

    #[tokio::test]
    async fn null_exit_without_shutdown_reports_failure() {
        assert!(lifecycle_with_exit(
            None,
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            false,
        )
        .await
        .is_err());
    }

    #[tokio::test]
    async fn structured_shutdown_authorizes_null_exit() {
        lifecycle_with_exit(
            Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":{"unexpected":true}})),
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            false,
        )
        .await
        .expect("official35/36 accept structured shutdown parameters");
    }

    #[tokio::test]
    async fn invalid_object_exit_does_not_authorize_null_exit() {
        assert!(lifecycle_with_exit(
            None,
            json!({"jsonrpc":"2.0","method":"exit","params":null}),
            false,
            true,
        )
        .await
        .is_err());
    }

    #[tokio::test]
    async fn eof_without_shutdown_reports_failure() {
        let (client, server) = tokio::io::duplex(1024);
        let (read, write) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(read, write, service, socket));
        drop(client);
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("EOF must finish")
            .expect("server task")
            .expect_err("official35/36 refuse EOF before shutdown");
    }

    #[tokio::test]
    async fn channel_reader_preserves_chunk_boundaries_bytes_and_errors() {
        let (sender, receiver) = mpsc::channel(3);
        sender.send(Ok(vec![0, 1, 2, 3])).await.expect("chunk1");
        sender.send(Ok(vec![4, 5])).await.expect("chunk2");
        sender
            .send(Err(io::Error::other("reader failure")))
            .await
            .expect("error");
        drop(sender);
        let mut reader = ChannelReader {
            receiver,
            bytes: Vec::new(),
            offset: 0,
        };
        let mut bytes = [0; 6];
        reader
            .read_exact(&mut bytes[..2])
            .await
            .expect("partial chunk");
        reader
            .read_exact(&mut bytes[2..])
            .await
            .expect("remaining chunks");
        assert_eq!(bytes, [0, 1, 2, 3, 4, 5]);
        let error = reader.read_u8().await.expect_err("propagate read error");
        assert_eq!(error.to_string(), "reader failure");
        assert_eq!(reader.read(&mut bytes).await.expect("EOF"), 0);
    }

    #[tokio::test]
    async fn exit_requests_after_shutdown_reply_then_leave_normal_exit_available() {
        for id in [json!(3), json!("exit-request")] {
            let (client, server) = tokio::io::duplex(16_384);
            let (input, output) = tokio::io::split(server);
            let (service, socket) = crate::build_service();
            let task = tokio::spawn(serve(input, output, service, socket));
            let (input, mut output) = tokio::io::split(client);
            let mut input = BufReader::new(input);
            send(
                &mut output,
                json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
            )
            .await;
            assert!(response(&mut input).await.get("result").is_some());
            send(
                &mut output,
                json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
            )
            .await;
            assert_eq!(response(&mut input).await.get("result"), Some(&Value::Null));
            send(
                &mut output,
                json!({"jsonrpc":"2.0","id":id,"method":"exit"}),
            )
            .await;
            let reply = tokio::time::timeout(Duration::from_secs(5), response(&mut input))
                .await
                .expect("an exit request must be refused without entering Exited");
            assert_eq!(reply.get("id"), Some(&id));
            assert_eq!(reply["error"]["code"], json!(-32600));
            assert!(reply.get("result").is_none());
            assert!(!task.is_finished());
            send(&mut output, json!({"jsonrpc":"2.0","method":"exit"})).await;
            tokio::time::timeout(Duration::from_secs(5), task)
                .await
                .expect("a later exit notification must finish with input open")
                .expect("no task panic")
                .expect("accepted shutdown authorizes exit");
            drop(output);
        }
    }

    #[tokio::test]
    async fn scalar_exit_parameters_finish_after_shutdown_with_input_open() {
        for params in [
            json!(false),
            json!(true),
            json!(0),
            json!(-1),
            json!("exit"),
        ] {
            for buffered in [false, true] {
                lifecycle_with_exit(
                    Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
                    json!({"jsonrpc":"2.0","method":"exit","params":params}),
                    buffered,
                    false,
                )
                .await
                .expect("native non-structured exit parameters are parameterless");
            }
        }
    }

    #[tokio::test]
    async fn scalar_exit_parameters_without_shutdown_report_failure() {
        for params in [json!(false), json!(1), json!("exit")] {
            assert!(lifecycle_with_exit(
                None,
                json!({"jsonrpc":"2.0","method":"exit","params":params}),
                false,
                false,
            )
            .await
            .is_err());
        }
    }

    struct FailingRead;

    impl AsyncRead for FailingRead {
        fn poll_read(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buffer: &mut ReadBuf<'_>,
        ) -> Poll<io::Result<()>> {
            Poll::Ready(Err(io::Error::new(
                io::ErrorKind::ConnectionReset,
                "chosen read failure",
            )))
        }
    }

    struct FailingWrite {
        flush_only: bool,
    }

    impl AsyncWrite for FailingWrite {
        fn poll_write(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            bytes: &[u8],
        ) -> Poll<io::Result<usize>> {
            if self.flush_only {
                Poll::Ready(Ok(bytes.len()))
            } else {
                Poll::Ready(Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "chosen write failure",
                )))
            }
        }

        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            if self.flush_only {
                Poll::Ready(Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "chosen flush failure",
                )))
            } else {
                Poll::Ready(Ok(()))
            }
        }

        fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
    }

    #[tokio::test]
    async fn serve_propagates_read_failure_without_a_task_panic() {
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(FailingRead, tokio::io::sink(), service, socket));
        let error = tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("read failure must terminate")
            .expect("read failure must not panic")
            .expect_err("read failure must propagate through serve");
        assert_eq!(error.kind(), io::ErrorKind::ConnectionReset);
        assert_eq!(error.to_string(), "chosen read failure");
    }

    async fn failing_output(flush_only: bool, expected: &str) {
        let (mut client, server) = tokio::io::duplex(16_384);
        let (input, _unused_output) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(input, FailingWrite { flush_only }, service, socket));
        send(
            &mut client,
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        )
        .await;
        let error = tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("output failure must terminate while input stays open")
            .expect("output failure must not panic")
            .expect_err("output failure must propagate through serve");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), expected);
        drop(client);
    }

    #[tokio::test]
    async fn serve_propagates_write_failure_with_input_open_without_a_panic() {
        failing_output(false, "chosen write failure").await;
    }

    #[tokio::test]
    async fn serve_propagates_flush_failure_with_input_open_without_a_panic() {
        failing_output(true, "chosen flush failure").await;
    }

    struct FailingShutdown;

    impl AsyncWrite for FailingShutdown {
        fn poll_write(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            bytes: &[u8],
        ) -> Poll<io::Result<usize>> {
            Poll::Ready(Ok(bytes.len()))
        }
        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
        fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "chosen shutdown failure",
            )))
        }
    }

    #[tokio::test]
    async fn serve_propagates_writer_shutdown_failure_with_input_open_without_a_panic() {
        let (mut client, server) = tokio::io::duplex(16_384);
        let (input, _unused_output) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(input, FailingShutdown, service, socket));
        let mut bytes = frame(
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        );
        bytes.extend(frame(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})));
        bytes.extend(frame(json!({"jsonrpc":"2.0","method":"exit"})));
        client.write_all(&bytes).await.expect("pipelined frames");
        let error = tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("writer shutdown failure must terminate with input open")
            .expect("writer shutdown failure must not panic")
            .expect_err("writer shutdown failure must propagate");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "chosen shutdown failure");
        drop(client);
    }

    type TestReader = BufReader<tokio::io::ReadHalf<tokio::io::DuplexStream>>;
    type TestWriter = tokio::io::WriteHalf<tokio::io::DuplexStream>;

    async fn connected() -> (
        tokio::task::JoinHandle<io::Result<()>>,
        TestReader,
        TestWriter,
    ) {
        let (client, server) = tokio::io::duplex(32_768);
        let (reader, writer) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(reader, writer, service, socket));
        let (reader, mut writer) = tokio::io::split(client);
        let mut reader = BufReader::new(reader);
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        )
        .await;
        assert!(reply_for(&mut reader, json!(1))
            .await
            .get("result")
            .is_some());
        (task, reader, writer)
    }

    async fn reply_for(reader: &mut TestReader, id: Value) -> Value {
        loop {
            let message = tokio::time::timeout(Duration::from_secs(5), response(reader))
                .await
                .expect("reply deadline");
            if message.get("id") == Some(&id) && message.get("method").is_none() {
                return message;
            }
        }
    }

    async fn registration(reader: &mut TestReader) -> Value {
        loop {
            let message = tokio::time::timeout(Duration::from_secs(5), response(reader))
                .await
                .expect("client request deadline");
            if message.get("method") == Some(&json!("client/registerCapability")) {
                assert!(message.get("id").is_some());
                assert_eq!(
                    message["params"]["registrations"][0]["method"],
                    json!("workspace/didChangeConfiguration")
                );
                return message;
            }
        }
    }

    #[tokio::test]
    async fn all_native_shutdown_parameter_shapes_authorize_exit() {
        for params in [
            json!(false),
            json!(0),
            json!("shutdown"),
            json!([]),
            json!({"unexpected":true}),
        ] {
            lifecycle(
                Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":params})),
                true,
            )
            .await
            .expect("official35/36 ignore shutdown parameters");
        }
    }

    #[tokio::test]
    async fn native_non_request_exit_ids_finish_with_input_open() {
        for id in [Value::Null, json!(false), json!({}), json!([])] {
            lifecycle_with_exit(
                Some(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"})),
                json!({"jsonrpc":"2.0","method":"exit","id":id}),
                true,
                false,
            )
            .await
            .expect("official35/36 fall back to exit notification");
        }
    }

    #[tokio::test]
    async fn pipelined_initialize_shutdown_exit_preserves_both_replies() {
        let (client, server) = tokio::io::duplex(32_768);
        let (reader, writer) = tokio::io::split(server);
        let (service, socket) = crate::build_service();
        let task = tokio::spawn(serve(reader, writer, service, socket));
        let (reader, mut writer) = tokio::io::split(client);
        let mut reader = BufReader::new(reader);
        let mut bytes = frame(
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        );
        bytes.extend(frame(
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":{}}),
        ));
        bytes.extend(frame(json!({"jsonrpc":"2.0","method":"exit"})));
        writer.write_all(&bytes).await.expect("pipelined frames");
        assert!(reply_for(&mut reader, json!(1))
            .await
            .get("result")
            .is_some());
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("pipelined exit deadline")
            .expect("server task")
            .expect("successful shutdown");
        drop(writer);
    }

    #[tokio::test]
    async fn real_client_registration_response_is_routed_bidirectionally() {
        let (task, mut reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","method":"initialized","params":{}}),
        )
        .await;
        let request = registration(&mut reader).await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":request["id"],"result":null}),
        )
        .await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
        )
        .await;
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        send(&mut writer, json!({"jsonrpc":"2.0","method":"exit"})).await;
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("exit deadline")
            .expect("server task")
            .expect("orderly exit");
        drop(writer);
    }

    #[tokio::test]
    async fn exit_does_not_wait_for_unanswered_client_registration() {
        let (task, mut reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","method":"initialized","params":{}}),
        )
        .await;
        let _unanswered = registration(&mut reader).await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
        )
        .await;
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        send(&mut writer, json!({"jsonrpc":"2.0","method":"exit"})).await;
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("unanswered registration cannot block exit")
            .expect("server task")
            .expect("orderly exit");
        drop(writer);
    }

    #[tokio::test]
    async fn response_and_invalid_json_buffered_after_exit_are_ignored() {
        let (task, mut reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
        )
        .await;
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        let mut bytes = frame(json!({"jsonrpc":"2.0","method":"exit"}));
        bytes.extend(frame(json!({"jsonrpc":"2.0","id":999,"result":null})));
        bytes.extend_from_slice(b"Content-Length: 1\r\n\r\n{");
        writer.write_all(&bytes).await.expect("buffered tail");
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("exit ignores buffered tail")
            .expect("server task")
            .expect("orderly exit");
        drop(writer);
    }

    #[tokio::test]
    async fn null_id_shutdown_without_parameters_is_refused() {
        let (task, _reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":null,"method":"shutdown"}),
        )
        .await;
        assert!(tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("refusal deadline")
            .expect("server task")
            .is_err());
        drop(writer);
    }

    #[tokio::test]
    async fn structured_exit_request_before_shutdown_is_refused_without_stopping() {
        let (task, mut reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":"exit-λ🧪","method":"exit","params":{}}),
        )
        .await;
        let reply = reply_for(&mut reader, json!("exit-λ🧪")).await;
        assert_eq!(
            reply["error"],
            json!({"code":-32601,"message":"No request handler found for 'exit'"})
        );
        assert!(reply.get("result").is_none());
        assert!(!task.is_finished());
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
        )
        .await;
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        send(&mut writer, json!({"jsonrpc":"2.0","method":"exit"})).await;
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("exit deadline")
            .expect("server task")
            .expect("orderly exit");
        drop(writer);
    }

    #[tokio::test]
    async fn eof_after_shutdown_is_orderly_without_an_exit_frame() {
        let (task, mut reader, mut writer) = connected().await;
        send(
            &mut writer,
            json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}),
        )
        .await;
        assert_eq!(
            reply_for(&mut reader, json!(2)).await.get("result"),
            Some(&Value::Null)
        );
        // A split half shares the duplex stream with reader; dropping the
        // write half alone does not close input while reader is retained.
        writer
            .shutdown()
            .await
            .expect("intentional client input EOF");
        drop(writer);
        tokio::time::timeout(Duration::from_secs(5), task)
            .await
            .expect("EOF deadline")
            .expect("server task")
            .expect("EOF after shutdown");
    }
}
