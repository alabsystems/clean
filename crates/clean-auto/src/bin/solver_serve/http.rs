// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal async HTTP/1.1 server primitives for `solver_serve`.
//!
//! No high-level framework (axum/hyper are not vendored offline): the service
//! reads a request line + headers (+ the body for `POST /ingest`) with
//! [`httparse`] over a `tokio::net::TcpStream`, dispatches to [`super::routes`],
//! and writes a single JSON response. This mirrors `mathverse_serve`'s and
//! `clean-server`'s raw-`tokio` posture.

use std::collections::HashMap;
use std::rc::Rc;

use anyhow::{Context, Result};
use percent_encoding::percent_decode_str;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

use super::routes::{self, AppState};

/// Maximum bytes read while parsing request headers.
const MAX_HEADER_BYTES: usize = 64 * 1024;
/// Maximum request body bytes accepted (for `POST /ingest`).
const MAX_BODY_BYTES: usize = 1 << 20;

/// A parsed inbound request.
pub(crate) struct Request {
    pub(crate) method: String,
    pub(crate) path: String,
    pub(crate) query: HashMap<String, String>,
    pub(crate) body: Vec<u8>,
}

/// A JSON response ready to serialize.
pub(crate) struct Response {
    pub(crate) status: u16,
    pub(crate) body: Vec<u8>,
}

impl Response {
    /// A JSON body with an explicit status code.
    pub(crate) fn json_with_status(status: u16, value: &serde_json::Value) -> Self {
        let body = serde_json::to_vec(value).unwrap_or_else(|_| b"{}".to_vec());
        Self { status, body }
    }

    /// A JSON error envelope.
    pub(crate) fn error(status: u16, message: &str) -> Self {
        Self::json_with_status(
            status,
            &serde_json::json!({ "error": message, "status": status }),
        )
    }
}

/// Reason phrase for the small set of status codes the service emits.
fn reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        202 => "Accepted",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        413 => "Payload Too Large",
        500 => "Internal Server Error",
        503 => "Service Unavailable",
        _ => "OK",
    }
}

/// Bind the listener and serve requests until the process is terminated.
///
/// Connections are handled **sequentially** on a single-threaded runtime; each
/// request is a cheap in-memory aggregation or an append. Cloud Run scales out
/// by instance count, so `state` is an `Rc`, not an `Arc`.
///
/// # Errors
/// Fails if the port cannot be bound.
pub(crate) async fn serve(state: Rc<AppState>, port: u16) -> Result<()> {
    let addr = format!("0.0.0.0:{port}");
    let listener = TcpListener::bind(&addr)
        .await
        .with_context(|| format!("failed to bind {addr}"))?;
    eprintln!("solver_serve listening on {addr}");

    loop {
        let (stream, _peer) = match listener.accept().await {
            Ok(pair) => pair,
            Err(e) => {
                eprintln!("accept error: {e}");
                continue;
            }
        };
        if let Err(e) = handle_connection(stream, &state).await {
            eprintln!("connection error: {e}");
        }
    }
}

/// Read one request, route it, and write the response.
async fn handle_connection(mut stream: TcpStream, state: &AppState) -> Result<()> {
    let request = match read_request(&mut stream).await? {
        Some(req) => req,
        None => {
            write_response(&mut stream, Response::error(400, "malformed request")).await?;
            return Ok(());
        }
    };
    let response = routes::dispatch(state, &request);
    write_response(&mut stream, response).await?;
    Ok(())
}

/// Read and parse the request line + headers (and the body, when present).
async fn read_request(stream: &mut TcpStream) -> Result<Option<Request>> {
    let mut buf = Vec::with_capacity(2048);
    let mut chunk = [0u8; 2048];

    let mut header_end = None;
    loop {
        let n = stream
            .read(&mut chunk)
            .await
            .context("socket read failed")?;
        if n == 0 {
            if buf.is_empty() {
                return Ok(None);
            }
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
        if let Some(pos) = find_header_end(&buf) {
            header_end = Some(pos);
            break;
        }
        if buf.len() > MAX_HEADER_BYTES {
            return Ok(None);
        }
    }

    let mut headers = [httparse::EMPTY_HEADER; 64];
    let mut req = httparse::Request::new(&mut headers);
    match req.parse(&buf) {
        Ok(httparse::Status::Complete(_) | httparse::Status::Partial) => {}
        Err(_) => return Ok(None),
    }

    let method = match req.method {
        Some(m) => m.to_string(),
        None => return Ok(None),
    };
    let raw_path = match req.path {
        Some(p) => p,
        None => return Ok(None),
    };
    let content_length = content_length(req.headers);
    let (path, query) = split_path_query(raw_path);

    let body = match (header_end, content_length) {
        (Some(end), Some(len)) if len > 0 => read_body(stream, &buf[end..], len).await?,
        _ => Vec::new(),
    };

    Ok(Some(Request {
        method,
        path,
        query,
        body,
    }))
}

/// Find the byte offset just past the `\r\n\r\n` header terminator, if present.
fn find_header_end(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n").map(|p| p + 4)
}

/// Parse the `Content-Length` header (case-insensitive), if present and valid.
fn content_length(headers: &[httparse::Header<'_>]) -> Option<usize> {
    headers
        .iter()
        .find(|h| h.name.eq_ignore_ascii_case("content-length"))
        .and_then(|h| std::str::from_utf8(h.value).ok())
        .and_then(|s| s.trim().parse::<usize>().ok())
}

/// Read the request body, given the bytes already buffered after the headers.
async fn read_body(stream: &mut TcpStream, prefix: &[u8], declared_len: usize) -> Result<Vec<u8>> {
    let want = declared_len.min(MAX_BODY_BYTES);
    let mut body = Vec::with_capacity(want.min(64 * 1024));
    body.extend_from_slice(&prefix[..prefix.len().min(want)]);
    let mut chunk = [0u8; 8192];
    while body.len() < want {
        let n = stream
            .read(&mut chunk)
            .await
            .context("socket read failed")?;
        if n == 0 {
            break;
        }
        let take = (want - body.len()).min(n);
        body.extend_from_slice(&chunk[..take]);
    }
    Ok(body)
}

/// Split a raw request target into a percent-decoded path and a query map.
fn split_path_query(raw: &str) -> (String, HashMap<String, String>) {
    let (path_part, query_part) = match raw.split_once('?') {
        Some((p, q)) => (p, q),
        None => (raw, ""),
    };
    let path = decode(path_part);
    let mut query = HashMap::new();
    for pair in query_part.split('&').filter(|s| !s.is_empty()) {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        query.insert(decode_plus(k), decode_plus(v));
    }
    (path, query)
}

/// Percent-decode a path segment.
fn decode(s: &str) -> String {
    percent_decode_str(s).decode_utf8_lossy().into_owned()
}

/// Percent-decode a query value, translating `+` to space.
fn decode_plus(s: &str) -> String {
    let replaced = s.replace('+', " ");
    percent_decode_str(&replaced)
        .decode_utf8_lossy()
        .into_owned()
}

/// Write a JSON response: status line, headers, then the body.
async fn write_response(stream: &mut TcpStream, response: Response) -> Result<()> {
    let head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: application/json\r\nConnection: close\r\n\
         Content-Length: {}\r\n\r\n",
        response.status,
        reason(response.status),
        response.body.len(),
    );
    stream.write_all(head.as_bytes()).await?;
    stream.write_all(&response.body).await?;
    stream.flush().await?;
    Ok(())
}
