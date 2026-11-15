// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What a peer without the launch token can make the server hold (plan item
//! `devsurface-server-trust-boundary`,
//! `docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`; the refusals themselves
//! are `trust_boundary_tests.rs`'s).
//!
//! Before its first message is judged, a connection costs the server a slot
//! (100 by default) and whatever of its first line has arrived. Two bounds,
//! each red before it existed:
//!
//! 1. a first TCP line longer than an `authenticate` request is refused before
//!    its newline arrives (the reader held a line of any length, until its
//!    newline);
//! 2. a connection that sends nothing is closed after the authenticate
//!    deadline, on TCP and on WebSocket, so peers without the token cannot
//!    hold every slot.
//!
//! The control at the end shows an admitted connection keeps the 10 MiB line
//! limit and outlives a line past it.

use std::net::SocketAddr;
use std::path::Path;
use std::time::Duration;

use clean_server::{ServerConfig, WebSocketConfig};
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::TcpStream;

/// The code a connection without the server's launch token is refused with.
const UNAUTHORIZED: i32 = -32006;

const UNAUTHORIZED_MISSING: &str = "unauthorized: a connection's first message must be the \
request {\"jsonrpc\":\"2.0\",\"method\":\"authenticate\",\"params\":{\"token\":\"<launch token>\"},\
\"id\":0}; `clean server` prints its launch token on standard error and writes it to its \
token file";

/// The refusal of a connection that sent no `authenticate` request within the
/// default deadline.
const UNAUTHORIZED_IDLE: &str =
    "unauthorized: the connection sent no authenticate request within 10000 ms of connecting";

/// A TCP server whose workspace root is `root`.
async fn serve_rooted(root: &Path) -> clean_server::ServerHandle {
    let config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(root.to_path_buf());
    clean_server::serve(config).await.expect("serve")
}

fn authenticate_request(token: &str) -> String {
    json!({
        "jsonrpc": "2.0",
        "method": "authenticate",
        "params": { "token": token },
        "id": 0,
    })
    .to_string()
}

/// The answer to `authenticate` with the server's launch token.
fn assert_authenticated(answer: &str) {
    let value: Value = serde_json::from_str(answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    assert_eq!(
        value,
        json!({ "jsonrpc": "2.0", "result": { "authenticated": true }, "id": 0 }),
        "the launch token admits the connection"
    );
}

/// Send `requests` in order on one TCP connection; the line answering each.
async fn exchange(addr: SocketAddr, requests: &[String]) -> Vec<String> {
    let stream = TcpStream::connect(addr).await.expect("connect");
    let (read, mut write) = stream.into_split();
    let mut lines = BufReader::new(read).lines();
    let mut answers = Vec::new();
    for request in requests {
        write
            .write_all(format!("{request}\n").as_bytes())
            .await
            .expect("write");
        answers.push(
            tokio::time::timeout(Duration::from_secs(120), lines.next_line())
                .await
                .expect("an answer within 120s")
                .expect("read")
                .expect("an answer line before the server closed"),
        );
    }
    answers
}

// ── 1. a first line longer than an authenticate request ──────────────────────

#[tokio::test]
async fn test_trust_boundary_an_oversize_first_line_is_refused_before_its_newline() {
    let scratch = tempfile::tempdir().expect("scratch");
    let handle = serve_rooted(scratch.path()).await;
    let mut stream = TcpStream::connect(handle.local_addr())
        .await
        .expect("connect");
    // Far more than an authenticate request needs, and no newline: a reader
    // with no bound waits for the rest of the line, holding all of it, for as
    // long as the peer keeps sending. (Less than the server's 8 KiB read
    // buffer, so its close leaves nothing unread and sends no reset.)
    stream.write_all(&[b'x'; 6000]).await.expect("write");
    let mut reader = BufReader::new(stream);
    let mut answer = String::new();
    tokio::time::timeout(Duration::from_secs(20), reader.read_line(&mut answer))
        .await
        .expect(
            "the server answers a first line past the authenticate limit within 20s, without \
             waiting for its newline",
        )
        .expect("read");
    let value: Value = serde_json::from_str(&answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    assert_eq!(
        value,
        json!({
            "jsonrpc": "2.0",
            "error": { "code": UNAUTHORIZED, "message": UNAUTHORIZED_MISSING },
            "id": null,
        }),
        "a first line past the authenticate limit is refused as presenting no token, before its \
         newline arrives"
    );
    let mut next = String::new();
    assert!(
        matches!(
            tokio::time::timeout(Duration::from_secs(5), reader.read_line(&mut next)).await,
            Ok(Ok(0))
        ),
        "the server closes a connection it refused"
    );
    handle.shutdown();
}

// ── 2. a connection that sends nothing ───────────────────────────────────────

#[tokio::test]
async fn test_trust_boundary_an_idle_connection_is_closed_and_frees_its_slot() {
    let scratch = tempfile::tempdir().expect("scratch");
    let mut config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(scratch.path().to_path_buf());
    // One connection at a time, so a peer that connects and sends nothing
    // holds the only slot.
    config.max_concurrent = 1;
    let handle = clean_server::serve(config).await.expect("serve");
    let addr = handle.local_addr();
    let idle = TcpStream::connect(addr)
        .await
        .expect("connect the idle peer");

    // The token holder connects after it (the listener takes connections in
    // the order they were made).
    let token = handle.launch_token().as_str().to_string();
    let answers = tokio::time::timeout(
        Duration::from_secs(40),
        exchange(addr, &[authenticate_request(&token)]),
    )
    .await
    .expect(
        "the token holder is served within 40s while a peer that sent nothing held the only \
         connection slot",
    );
    assert_authenticated(&answers[0]);

    // The idle peer is told why, and closed.
    let mut reader = BufReader::new(idle);
    let mut answer = String::new();
    tokio::time::timeout(Duration::from_secs(40), reader.read_line(&mut answer))
        .await
        .expect("the idle peer is answered within 40s")
        .expect("read");
    let value: Value = serde_json::from_str(&answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    assert_eq!(
        value,
        json!({
            "jsonrpc": "2.0",
            "error": { "code": UNAUTHORIZED, "message": UNAUTHORIZED_IDLE },
            "id": null,
        })
    );
    let mut next = String::new();
    assert!(
        matches!(
            tokio::time::timeout(Duration::from_secs(5), reader.read_line(&mut next)).await,
            Ok(Ok(0))
        ),
        "the server closes the idle connection"
    );
    handle.shutdown();
}

#[tokio::test]
async fn test_trust_boundary_an_idle_websocket_connection_is_closed_and_frees_its_slot() {
    use futures_util::{SinkExt, StreamExt};
    use tokio::io::AsyncReadExt;
    use tokio_tungstenite::tungstenite::Message;

    let mut config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().expect("addr"));
    config.max_concurrent = 1;
    let handle = clean_server::serve_websocket(config)
        .await
        .expect("serve websocket");
    let addr = handle.local_addr();
    let token = handle.launch_token().as_str().to_string();

    // A peer that opens a socket and starts no handshake holds the only slot.
    let mut silent = TcpStream::connect(addr)
        .await
        .expect("connect the silent peer");
    let (mut ws, _) = tokio::time::timeout(
        Duration::from_secs(40),
        tokio_tungstenite::connect_async(format!("ws://{addr}")),
    )
    .await
    .expect(
        "the token holder's handshake completes within 40s while a peer that sent nothing held \
         the only connection slot",
    )
    .expect("handshake");
    ws.send(Message::Text(authenticate_request(&token).into()))
        .await
        .expect("send");
    match tokio::time::timeout(Duration::from_secs(20), ws.next())
        .await
        .expect("an answer within 20s")
    {
        Some(Ok(Message::Text(text))) => assert_authenticated(&text),
        other => panic!("the server answered no text: {other:?}"),
    }
    // The silent peer was closed with nothing sent to it.
    let mut buf = [0u8; 256];
    let read = tokio::time::timeout(Duration::from_secs(40), silent.read(&mut buf))
        .await
        .expect("the silent peer is closed within 40s")
        .expect("read");
    assert_eq!(
        read,
        0,
        "the server answered a peer that never started a handshake: {:?}",
        String::from_utf8_lossy(&buf[..read])
    );
    ws.close(None).await.expect("close");

    // A peer that completes the handshake and sends nothing is told why.
    let (mut quiet, _) = tokio::time::timeout(
        Duration::from_secs(40),
        tokio_tungstenite::connect_async(format!("ws://{addr}")),
    )
    .await
    .expect("the quiet peer's handshake completes within 40s")
    .expect("handshake");
    match tokio::time::timeout(Duration::from_secs(40), quiet.next())
        .await
        .expect("the quiet peer is answered within 40s")
    {
        Some(Ok(Message::Text(text))) => {
            let value: Value = serde_json::from_str(&text).expect("JSON");
            assert_eq!(
                value,
                json!({
                    "jsonrpc": "2.0",
                    "error": { "code": UNAUTHORIZED, "message": UNAUTHORIZED_IDLE },
                    "id": null,
                })
            );
        }
        other => panic!("the server answered the quiet peer no text: {other:?}"),
    }
    handle.shutdown();
}

// ── Control: an admitted connection ──────────────────────────────────────────

#[tokio::test]
async fn test_trust_boundary_control_an_admitted_connection_outlives_an_overlong_line() {
    let scratch = tempfile::tempdir().expect("scratch");
    let handle = serve_rooted(scratch.path()).await;
    let token = handle.launch_token().as_str().to_string();
    // 16 bytes past the 10 MiB line limit (the newline makes it 17).
    let overlong = "x".repeat(10 * 1024 * 1024 + 16);
    let answers = exchange(
        handle.local_addr(),
        &[
            authenticate_request(&token),
            overlong,
            r#"{"jsonrpc":"2.0","method":"serverInfo","id":1}"#.to_string(),
        ],
    )
    .await;
    assert_authenticated(&answers[0]);
    let refused: Value = serde_json::from_str(&answers[1]).expect("JSON");
    assert_eq!(
        refused,
        json!({
            "jsonrpc": "2.0",
            "error": {
                "code": -32600,
                "message": "Line too long: 10485777 bytes exceeds 10485760 limit",
            },
            "id": null,
        })
    );
    let info: Value = serde_json::from_str(&answers[2]).expect("JSON");
    assert_eq!(
        info["result"]["destructive_methods"],
        json!(["saveEnvironment", "loadEnvironment", "importModule"]),
        "the admitted connection is still served after its overlong line: {info}"
    );
    handle.shutdown();
}
