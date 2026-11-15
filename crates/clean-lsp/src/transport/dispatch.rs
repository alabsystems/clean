// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bidirectional service execution with fallible input, output and shutdown.

use super::framing::{self, Incoming, Outgoing, ReadError};
use crate::CleanBackend;
use futures_util::stream::{self, AbortHandle, FuturesUnordered};
use futures_util::{Sink, SinkExt, Stream, StreamExt};
use std::future::{poll_fn, Future};
use std::io;
use std::pin::Pin;
use tokio::io::{AsyncRead, AsyncWrite, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, oneshot};
use tower_lsp::jsonrpc::{Error, Id, Request, Response};
use tower_lsp::{ClientSocket, ExitedError, LspService};
use tower_service::Service;

type PendingReply = Pin<Box<dyn Future<Output = io::Result<Option<Response>>> + Send>>;
const MAX_CONCURRENCY: usize = 4;
const REQUEST_QUEUE_SIZE: usize = 100;

fn invalid_message(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn no_request_handler(id: Id, method: &str) -> Response {
    let mut error = Error::method_not_found();
    error.message = format!("No request handler found for '{method}'").into();
    Response::from_error(id, error)
}

async fn emit(responses: &mpsc::Sender<Outgoing>, response: Response) -> io::Result<()> {
    responses
        .send(Outgoing::Response(response))
        .await
        .map_err(|_| io::Error::new(io::ErrorKind::BrokenPipe, "LSP output queue closed"))
}

async fn call(
    service: &mut LspService<CleanBackend>,
    request: Request,
) -> io::Result<Option<Response>> {
    poll_fn(|cx| service.poll_ready(cx))
        .await
        .map_err(io::Error::other)?;
    service.call(request).await.map_err(io::Error::other)
}

async fn read_input<R, S>(
    reader: R,
    mut service: LspService<CleanBackend>,
    mut client_responses: S,
    tasks: mpsc::Sender<PendingReply>,
    responses: mpsc::Sender<Outgoing>,
) -> io::Result<()>
where
    R: AsyncRead + Unpin,
    S: Sink<Response, Error = ExitedError> + Unpin,
{
    let mut reader = BufReader::new(reader);
    let mut initialized = false;
    let mut shutdown = false;
    loop {
        let message = match framing::read(&mut reader).await {
            Ok(Some(message)) => message,
            Ok(None) if shutdown => return Ok(()),
            Ok(None) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "LSP input closed before successful shutdown",
                ))
            }
            Err(ReadError::Io(error)) => return Err(error),
            Err(ReadError::Protocol(_)) if shutdown => return Ok(()),
            Err(ReadError::Protocol(message)) => return Err(invalid_message(&message)),
            Err(ReadError::Unsupported(message)) => {
                return Err(io::Error::new(io::ErrorKind::Unsupported, message))
            }
        };
        if !initialized {
            let Incoming::Request(request) = message else {
                return Err(invalid_message("expected initialize request"));
            };
            if request.method() != "initialize"
                || request.id().is_none()
                || request.params().is_none()
            {
                return Err(invalid_message("expected initialize request"));
            }
            let response = call(&mut service, request)
                .await?
                .filter(Response::is_ok)
                .ok_or_else(|| invalid_message("initialize request was refused"))?;
            initialized = true;
            emit(&responses, response).await?;
            continue;
        }
        let Incoming::Request(request) = message else {
            if let Incoming::Response(response) = message {
                if !shutdown {
                    client_responses
                        .send(response)
                        .await
                        .map_err(io::Error::other)?;
                }
            }
            continue;
        };
        if shutdown {
            if let Some(id) = request.id() {
                let mut error = Error::invalid_request();
                error.message = "Request received after 'shutdown' request.".into();
                emit(&responses, Response::from_error(id.clone(), error)).await?;
            } else if request.method() == "exit" && request.params().is_none() {
                // Await the actual exit handler, then ignore all buffered tail.
                call(&mut service, request).await?;
                return Ok(());
            }
            continue;
        }
        match (request.method(), request.id()) {
            ("shutdown", Some(id)) => {
                // Lean ignores shutdown params. Complete it before a buffered
                // exit can cancel its future or race authorization.
                let request = Request::build("shutdown").id(id.clone()).finish();
                let response = call(&mut service, request)
                    .await?
                    .filter(Response::is_ok)
                    .ok_or_else(|| invalid_message("shutdown request was refused"))?;
                shutdown = true;
                emit(&responses, response).await?;
                continue;
            }
            ("exit", None) if request.params().is_none() => {
                return Err(invalid_message(
                    "LSP exit received before successful shutdown",
                ));
            }
            ("shutdown", None) if request.params().is_none() => {
                return Err(invalid_message(
                    "shutdown notification requires structured parameters",
                ))
            }
            ("exit" | "shutdown", None) => continue,
            (method @ ("exit" | "$/lean/rpc/release" | "$/lean/rpc/keepAlive"), Some(id)) => {
                if request.params().is_none() {
                    return Err(invalid_message("request requires structured parameters"));
                }
                emit(&responses, no_request_handler(id.clone(), method)).await?;
                continue;
            }
            _ => {}
        }
        if request.params().is_none() {
            return Err(invalid_message("message requires structured parameters"));
        }
        if matches!(
            request.method(),
            "$/lean/rpc/release" | "$/lean/rpc/keepAlive"
        ) {
            // These real callbacks are synchronous notifications. Preserve
            // their order relative to later frames without blocking on any
            // server-to-client request.
            if let Some(response) = call(&mut service, request).await? {
                emit(&responses, response).await?;
            }
            continue;
        }
        poll_fn(|cx| service.poll_ready(cx))
            .await
            .map_err(io::Error::other)?;
        let future = service.call(request);
        let future: PendingReply = Box::pin(async move { future.await.map_err(io::Error::other) });
        // Retain the existing 100-request bound. A full queue must refuse the
        // connection rather than block reading client responses indefinitely.
        tasks.try_send(future).map_err(|error| match error {
            mpsc::error::TrySendError::Full(_) => {
                io::Error::new(io::ErrorKind::WouldBlock, "LSP request queue is full")
            }
            mpsc::error::TrySendError::Closed(_) => {
                io::Error::new(io::ErrorKind::BrokenPipe, "LSP task queue closed")
            }
        })?;
    }
}

async fn process_tasks(
    mut tasks: mpsc::Receiver<PendingReply>,
    responses: mpsc::Sender<Outgoing>,
    mut stop: oneshot::Receiver<()>,
) -> io::Result<()> {
    let mut running: FuturesUnordered<PendingReply> = FuturesUnordered::new();
    let mut incoming = true;
    loop {
        tokio::select! {
            biased;
            result = running.next(), if !running.is_empty() => {
                if let Some(Some(response)) = result.transpose()? { emit(&responses, response).await?; }
            }
            task = tasks.recv(), if incoming && running.len() < MAX_CONCURRENCY => {
                match task { Some(future) => running.push(future), None => incoming = false }
            }
            _ = &mut stop => {
                // An initialized notification may still await an unanswered
                // client/registerCapability request. It cannot keep exit alive.
                tasks.close();running.clear();
                while tasks.try_recv().is_ok() {}
                return Ok(());
            }
            else => return Ok(()),
        }
    }
}

async fn write_output<W, S>(
    writer: W,
    mut client_requests: S,
    mut responses: mpsc::Receiver<Outgoing>,
) -> io::Result<()>
where
    W: AsyncWrite,
    S: Stream<Item = Request> + Unpin,
{
    let mut writer = Box::pin(writer);
    let mut requests_open = true;
    let mut responses_open = true;
    loop {
        let message = tokio::select! {
            request = client_requests.next(), if requests_open => match request {
                Some(request) => Some(Outgoing::Request(request)),
                None => { requests_open = false; None }
            },
            response = responses.recv(), if responses_open => match response {
                Some(response) => Some(response),
                None => { responses_open = false; None }
            },
            else => break,
        };
        let Some(message) = message else {
            continue;
        };
        let body = serde_json::to_vec(&message)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        writer
            .write_all(format!("Content-Length: {}\r\n\r\n", body.len()).as_bytes())
            .await?;
        writer.write_all(&body).await?;
        writer.flush().await?;
    }
    writer.shutdown().await
}

pub(super) async fn serve<R, W>(
    reader: R,
    writer: W,
    service: LspService<CleanBackend>,
    socket: ClientSocket,
) -> io::Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite,
{
    let (requests, client_responses) = socket.split();
    let (requests, abort): (_, AbortHandle) = stream::abortable(requests);
    let (tasks_tx, tasks_rx) = mpsc::channel(REQUEST_QUEUE_SIZE);
    let (responses_tx, responses_rx) = mpsc::channel(1);
    let (stop, stopping) = oneshot::channel();
    let input_responses = responses_tx.clone();
    let reading = async move {
        let result = read_input(reader, service, client_responses, tasks_tx, input_responses).await;
        abort.abort();
        let _ = stop.send(());
        // Drain responses already committed before reporting a read failure.
        Ok::<_, io::Error>(result)
    };
    let (_, read_result, _) = tokio::try_join!(
        write_output(writer, requests, responses_rx),
        reading,
        process_tasks(tasks_rx, responses_tx, stopping),
    )?;
    read_result
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::time::Duration;

    fn frame(message: serde_json::Value) -> Vec<u8> {
        let body = serde_json::to_vec(&message).expect("encode frame");
        let mut bytes = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        bytes.extend(body);
        bytes
    }

    #[tokio::test]
    async fn full_real_request_queue_refuses_instead_of_blocking_the_client_response_reader() {
        let mut bytes = frame(
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}),
        );
        for id in 2..=(REQUEST_QUEUE_SIZE + 2) {
            bytes.extend(frame(
                json!({"jsonrpc":"2.0","id":id,"method":"textDocument/hover","params":{}}),
            ));
        }
        let (service, socket) = crate::build_service();
        let (_client_requests, client_responses) = socket.split();
        // Keep all actual service futures pending to deterministically exhaust
        // the same queue used by serve; no handler or checker is replaced.
        let (tasks, pending_tasks) = mpsc::channel(REQUEST_QUEUE_SIZE);
        let (responses, mut replies) = mpsc::channel(1);
        let error = tokio::time::timeout(
            Duration::from_secs(5),
            read_input(
                bytes.as_slice(),
                service,
                client_responses,
                tasks,
                responses,
            ),
        )
        .await
        .expect("full queue must terminate without waiting for a client response")
        .expect_err("full queue must refuse");
        assert_eq!(error.kind(), io::ErrorKind::WouldBlock);
        assert_eq!(error.to_string(), "LSP request queue is full");
        assert_eq!(pending_tasks.len(), REQUEST_QUEUE_SIZE);
        let Outgoing::Response(initialize) =
            replies.try_recv().expect("committed initialize reply")
        else {
            panic!("expected initialize response");
        };
        assert_eq!(initialize.id(), &Id::Number(1));
        assert!(initialize.is_ok());
    }
}
