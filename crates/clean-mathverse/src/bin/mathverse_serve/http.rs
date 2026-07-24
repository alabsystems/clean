// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal async HTTP/1.1 server primitives for `mathverse_serve`.
//!
//! No high-level framework (axum/hyper are not vendored offline in this
//! workspace): the service reads a request line + headers with [`httparse`]
//! over a `tokio::net::TcpStream`, dispatches to [`super::routes`], and writes
//! a single response. This mirrors `clean-server`'s raw-`tokio` posture. The
//! surface is mostly read-only GET; the one body-bearing route is
//! `POST /submit`, whose body (a candidate declaration) is read up to
//! [`MAX_BODY_BYTES`] and passed to the queue front-end (no signing key).

use std::collections::HashMap;
use std::rc::Rc;

use anyhow::{Context, Result};
use percent_encoding::percent_decode_str;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

use super::routes::{self, AppState};

/// Maximum bytes we read while parsing request headers. The surface has short
/// paths; anything past this is a malformed or hostile request.
const MAX_HEADER_BYTES: usize = 64 * 1024;

/// Maximum request body bytes accepted (for `POST /submit`). Matches the
/// submission queue's own 1 MiB limit; a larger body is truncated to this cap
/// and the queue's size check rejects it.
const MAX_BODY_BYTES: usize = 1 << 20;

/// A parsed inbound request: method, decoded path, query parameters, and the
/// request body (empty for GET; the candidate JSON for `POST /submit`).
pub(crate) struct Request {
    pub(crate) method: String,
    pub(crate) path: String,
    pub(crate) query: HashMap<String, String>,
    pub(crate) body: Vec<u8>,
}

/// A response ready to serialize: status, content type, and a body that is
/// either an in-memory buffer or a streamed file (for shard downloads).
pub(crate) struct Response {
    pub(crate) status: u16,
    pub(crate) content_type: &'static str,
    pub(crate) body: Body,
    /// Extra headers (e.g. `Location` for a redirect).
    pub(crate) extra_headers: Vec<(String, String)>,
}

/// Response body source.
pub(crate) enum Body {
    /// An in-memory buffer (JSON, plain text).
    Bytes(Vec<u8>),
    /// A local file to stream as `application/octet-stream` (shard download).
    File(std::path::PathBuf),
    /// No body (e.g. 302 redirect).
    Empty,
}

impl Response {
    /// 200 with a JSON body.
    pub(crate) fn json(value: &serde_json::Value) -> Self {
        Self::json_with_status(200, value)
    }

    /// A JSON body with an explicit status code (e.g. 202 Accepted for a staged
    /// `/submit`, or 400 for a malformed candidate).
    pub(crate) fn json_with_status(status: u16, value: &serde_json::Value) -> Self {
        let body = serde_json::to_vec(value).unwrap_or_else(|_| b"{}".to_vec());
        Self {
            status,
            content_type: "application/json",
            body: Body::Bytes(body),
            extra_headers: Vec::new(),
        }
    }

    /// A plain-text response with the given status.
    pub(crate) fn text(status: u16, body: &str) -> Self {
        Self {
            status,
            content_type: "text/plain; charset=utf-8",
            body: Body::Bytes(body.as_bytes().to_vec()),
            extra_headers: Vec::new(),
        }
    }

    /// A JSON error envelope with the given status.
    pub(crate) fn error(status: u16, message: &str) -> Self {
        Self::json(&serde_json::json!({ "error": message, "status": status })).with_status(status)
    }

    /// A 302 redirect to `location`.
    pub(crate) fn redirect(location: String) -> Self {
        Self {
            status: 302,
            content_type: "text/plain; charset=utf-8",
            body: Body::Empty,
            extra_headers: vec![("Location".to_string(), location)],
        }
    }

    /// Stream a local file as `application/octet-stream`.
    pub(crate) fn file(path: std::path::PathBuf) -> Self {
        Self {
            status: 200,
            content_type: "application/octet-stream",
            body: Body::File(path),
            extra_headers: Vec::new(),
        }
    }

    fn with_status(mut self, status: u16) -> Self {
        self.status = status;
        self
    }
}

/// Reason phrase for the small set of status codes the service emits.
fn reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        202 => "Accepted",
        302 => "Found",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        413 => "Payload Too Large",
        500 => "Internal Server Error",
        501 => "Not Implemented",
        503 => "Service Unavailable",
        _ => "OK",
    }
}

/// Bind the listener and serve requests until the process is terminated.
///
/// Connections are handled **sequentially** on a single-threaded runtime. This
/// is deliberate: the loaded [`crate::library::MathverseLibrary`] is `!Sync`
/// (it carries a lazily-rebuilt `RefCell<BM25Index>` and is documented as
/// thread-local), so it cannot be shared across worker tasks. A read-only
/// browse/search/download front-end does not need per-connection concurrency —
/// Cloud Run scales out by instance count, and each request is a cheap in-memory
/// lookup or a streamed file. `state` is therefore an `Rc`, not an `Arc`.
///
/// # Errors
/// Fails if the port cannot be bound.
pub(crate) async fn serve(state: Rc<AppState>, port: u16) -> Result<()> {
    let addr = format!("0.0.0.0:{port}");
    let listener = TcpListener::bind(&addr)
        .await
        .with_context(|| format!("failed to bind {addr}"))?;
    eprintln!("mathverse_serve listening on {addr}");

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
        // Empty / unparseable read: answer 400 and close.
        None => {
            write_response(&mut stream, Response::error(400, "malformed request")).await?;
            return Ok(());
        }
    };

    let response = routes::dispatch(state, &request);
    write_response(&mut stream, response).await?;
    Ok(())
}

/// Read and parse the request line + headers (and the body for a body-bearing
/// request) from the stream.
///
/// Returns `Ok(None)` for a malformed or oversized request so the caller can
/// answer 400. The body is read for any request carrying a `Content-Length`
/// (i.e. `POST /submit`), up to [`MAX_BODY_BYTES`].
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
            // Connection closed before a full header block arrived.
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
    let parse_result = req.parse(&buf);
    match parse_result {
        Ok(httparse::Status::Complete(_)) | Ok(httparse::Status::Partial) => {}
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

    // Read the body if the request declares one. Bytes already buffered past the
    // header terminator are the start of the body.
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

/// Read the request body, given the bytes already buffered after the headers and
/// the declared content length. Caps the total at [`MAX_BODY_BYTES`]; a larger
/// declared length is clamped so the downstream size check rejects it without
/// us buffering an unbounded body.
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

/// Split a raw request target into a percent-decoded path and a parsed query
/// map. Decoding is lossy-safe (invalid UTF-8 sequences fall back to the raw
/// bytes via `String::from_utf8_lossy`).
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

/// Percent-decode a query value, also translating `+` to space (the
/// `application/x-www-form-urlencoded` convention).
fn decode_plus(s: &str) -> String {
    let replaced = s.replace('+', " ");
    percent_decode_str(&replaced)
        .decode_utf8_lossy()
        .into_owned()
}

/// Write a response: status line, headers, then the body (buffered or streamed).
async fn write_response(stream: &mut TcpStream, response: Response) -> Result<()> {
    let mut head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nConnection: close\r\n",
        response.status,
        reason(response.status),
        response.content_type,
    );
    for (k, v) in &response.extra_headers {
        head.push_str(&format!("{k}: {v}\r\n"));
    }

    match response.body {
        Body::Bytes(bytes) => {
            head.push_str(&format!("Content-Length: {}\r\n\r\n", bytes.len()));
            stream.write_all(head.as_bytes()).await?;
            stream.write_all(&bytes).await?;
        }
        Body::Empty => {
            head.push_str("Content-Length: 0\r\n\r\n");
            stream.write_all(head.as_bytes()).await?;
        }
        Body::File(path) => {
            let len = tokio::fs::metadata(&path)
                .await
                .map(|m| m.len())
                .unwrap_or(0);
            head.push_str(&format!("Content-Length: {len}\r\n\r\n"));
            stream.write_all(head.as_bytes()).await?;
            stream_file(stream, &path).await?;
        }
    }
    stream.flush().await?;
    Ok(())
}

/// Stream a file body to the socket in fixed-size chunks.
async fn stream_file(stream: &mut TcpStream, path: &std::path::Path) -> Result<()> {
    let mut file = tokio::fs::File::open(path)
        .await
        .with_context(|| format!("failed to open shard {}", path.display()))?;
    let mut chunk = vec![0u8; 64 * 1024];
    loop {
        let n = file.read(&mut chunk).await?;
        if n == 0 {
            break;
        }
        stream.write_all(&chunk[..n]).await?;
    }
    Ok(())
}
