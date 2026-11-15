// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean's LSP envelope and header rules, with physical I/O errors preserved.

use serde::Serialize;
use serde_json::Value;
use std::io;
use tokio::io::{AsyncBufReadExt, AsyncRead, AsyncReadExt, BufReader};
use tower_lsp::jsonrpc::{Id, Request, Response};

pub(super) enum Incoming {
    Request(Request),
    Response(Response),
}

#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Outgoing {
    Request(Request),
    Response(Response),
}

#[derive(Debug, thiserror::Error)]
pub(super) enum ReadError {
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error("{0}")]
    Protocol(String),
    #[error("{0}")]
    Unsupported(String),
}

fn request_id(value: Option<&Value>) -> Result<Option<Id>, ReadError> {
    match value {
        Some(Value::String(value)) => Ok(Some(Id::String(value.clone()))),
        Some(Value::Number(value)) => value.as_i64().map(Id::Number).map(Some).ok_or_else(|| {
            ReadError::Unsupported(
                "LSP numeric identifiers outside the signed 64-bit range are unsupported".into(),
            )
        }),
        // Lean's Message.fromJson? tries a request first, then a notification.
        // Null/bool/object/array identifiers do not parse as RequestID.
        _ => Ok(None),
    }
}

fn decode(body: &[u8]) -> Result<Incoming, ReadError> {
    let value: Value =
        serde_json::from_slice(body).map_err(|error| ReadError::Protocol(error.to_string()))?;
    let object = value
        .as_object()
        .ok_or_else(|| ReadError::Protocol("LSP message must be an object".into()))?;
    if object.get("jsonrpc").and_then(Value::as_str) != Some("2.0") {
        return Err(ReadError::Protocol(
            "LSP message requires JSON-RPC 2.0".into(),
        ));
    }
    let id = request_id(object.get("id"))?;
    if let Some(method) = object.get("method").and_then(Value::as_str) {
        let mut request = Request::build(method.to_owned());
        if let Some(id) = id {
            request = request.id(id);
        }
        if let Some(params) = object
            .get("params")
            .filter(|params| params.is_object() || params.is_array())
        {
            request = request.params(params.clone());
        }
        return Ok(Incoming::Request(request.finish()));
    }
    if id.is_none() {
        return Err(ReadError::Protocol(
            "LSP response requires a numeric or string identifier".into(),
        ));
    }
    serde_json::from_value(value)
        .map(Incoming::Response)
        .map_err(|error| ReadError::Protocol(error.to_string()))
}

pub(super) async fn read<R: AsyncRead + Unpin>(
    reader: &mut BufReader<R>,
) -> Result<Option<Incoming>, ReadError> {
    let mut length = None;
    let mut line = Vec::new();
    let mut any_header = false;
    loop {
        line.clear();
        if reader.read_until(b'\n', &mut line).await? == 0 {
            return if any_header {
                Err(ReadError::Protocol("incomplete LSP headers".into()))
            } else {
                Ok(None)
            };
        }
        any_header = true;
        if line == b"\r\n" {
            break;
        }
        if !line.ends_with(b"\r\n") {
            return Err(ReadError::Protocol("LSP header requires CRLF".into()));
        }
        let header = std::str::from_utf8(&line[..line.len() - 2])
            .map_err(|error| ReadError::Protocol(error.to_string()))?;
        let (name, value) = header
            .split_once(": ")
            .ok_or_else(|| ReadError::Protocol("invalid LSP header field".into()))?;
        // Lean's fields.lookup selects the first exact Content-Length field.
        if name == "Content-Length" && length.is_none() {
            if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
                return Err(ReadError::Protocol(
                    "LSP Content-Length must be a natural number".into(),
                ));
            }
            length = Some(
                value
                    .parse::<u64>()
                    .map_err(|error| ReadError::Unsupported(error.to_string()))?,
            );
        }
    }
    let length = length.ok_or_else(|| ReadError::Protocol("missing LSP Content-Length".into()))?;
    // Grow with received bytes; an untrusted length must not allocate eagerly.
    let mut body = Vec::new();
    let received = reader.take(length).read_to_end(&mut body).await?;
    if u64::try_from(received).ok() != Some(length) {
        return Err(ReadError::Protocol("incomplete LSP body".into()));
    }
    decode(&body).map(Some)
}
