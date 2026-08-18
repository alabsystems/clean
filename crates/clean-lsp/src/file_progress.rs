// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean4-compatible `$/lean/fileProgress` notification types.
//!
//! The server sends this notification to the client while a file is being
//! processed. The Lean 4 VS Code extension uses it to draw the orange
//! progress bar in the gutter and to gate infoview refresh timing: a
//! notification with a non-empty `processing` array means the covered ranges
//! are still being elaborated, and a terminal notification with an empty
//! `processing` array means the file is fully processed.
//!
//! Wire shapes mirror `Lean.Data.Lsp.Extra`:
//! `LeanFileProgressParams`, `LeanFileProgressProcessingInfo`, and
//! `LeanFileProgressKind` (serialized as the numbers `1` = processing,
//! `2` = fatalError).
//!
//! Source: Lean team, "Lean.Data.Lsp.Extra"
//! <https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html>

use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Range, VersionedTextDocumentIdentifier};

/// Error returned when a `$/lean/fileProgress` `kind` value is out of range.
///
/// Lean encodes the kind as `1` (processing) or `2` (fatalError); any other
/// number is a protocol violation and is rejected rather than coerced.
#[derive(Debug, Clone, thiserror::Error)]
#[error("invalid LeanFileProgressKind value: {0} (expected 1 = processing or 2 = fatalError)")]
pub struct InvalidFileProgressKind(u8);

/// Progress kind for a processing range.
/// Source: Lean.Data.Lsp.Extra, LeanFileProgressKind
///
/// Serialized as a bare number on the wire (`1` = processing,
/// `2` = fatalError), matching Lean's `ToJson LeanFileProgressKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(try_from = "u8", into = "u8")]
pub enum LeanFileProgressKind {
    /// The range is still being processed (wire value `1`).
    #[default]
    Processing,
    /// Processing aborted with a fatal error (wire value `2`).
    FatalError,
}

impl From<LeanFileProgressKind> for u8 {
    fn from(kind: LeanFileProgressKind) -> Self {
        match kind {
            LeanFileProgressKind::Processing => 1,
            LeanFileProgressKind::FatalError => 2,
        }
    }
}

impl TryFrom<u8> for LeanFileProgressKind {
    type Error = InvalidFileProgressKind;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Processing),
            2 => Ok(Self::FatalError),
            other => Err(InvalidFileProgressKind(other)),
        }
    }
}

/// One still-being-processed range of the file.
/// Source: Lean.Data.Lsp.Extra, LeanFileProgressProcessingInfo
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanFileProgressProcessingInfo {
    /// Range that is still being processed.
    pub range: Range,
    /// Kind of progress. Optional on the wire in Lean (defaults to
    /// processing), so deserialization tolerates its absence.
    #[serde(default)]
    pub kind: LeanFileProgressKind,
}

impl LeanFileProgressProcessingInfo {
    /// Build a `kind = processing` info for `range`, the shape the server
    /// emits while elaboration is still covering `range`.
    #[must_use]
    pub fn processing(range: Range) -> Self {
        Self {
            range,
            kind: LeanFileProgressKind::Processing,
        }
    }
}

/// Parameters of the `$/lean/fileProgress` notification.
/// Source: Lean.Data.Lsp.Extra, LeanFileProgressParams
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanFileProgressParams {
    /// Document (with version) the progress applies to.
    pub text_document: VersionedTextDocumentIdentifier,
    /// Ranges still being processed. Empty means processing has finished
    /// (the terminal notification).
    pub processing: Vec<LeanFileProgressProcessingInfo>,
}

/// Marker type wiring `LeanFileProgressParams` into tower-lsp's typed
/// server-to-client notification plumbing
/// (`Client::send_notification::<LeanFileProgress>`).
#[derive(Debug)]
pub enum LeanFileProgress {}

impl tower_lsp::lsp_types::notification::Notification for LeanFileProgress {
    type Params = LeanFileProgressParams;
    const METHOD: &'static str = "$/lean/fileProgress";
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};
    use std::time::Duration;
    use tokio::io::{AsyncReadExt, AsyncWriteExt, DuplexStream, ReadHalf, WriteHalf};
    use tower_lsp::lsp_types::{Position, Url};

    #[test]
    fn test_file_progress_params_serialize_matches_lean_wire_shape() {
        let params = LeanFileProgressParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: Url::parse("file:///a.lean").expect("static test URI"),
                version: 3,
            },
            processing: vec![LeanFileProgressProcessingInfo::processing(Range::new(
                Position::new(0, 0),
                Position::new(2, 0),
            ))],
        };

        let value = serde_json::to_value(&params).expect("serialize fileProgress params");
        assert_eq!(
            value,
            json!({
                "textDocument": { "uri": "file:///a.lean", "version": 3 },
                "processing": [{
                    "range": {
                        "start": { "line": 0, "character": 0 },
                        "end": { "line": 2, "character": 0 }
                    },
                    "kind": 1
                }]
            })
        );
    }

    #[test]
    fn test_file_progress_kind_missing_on_wire_defaults_to_processing() {
        let info: LeanFileProgressProcessingInfo = serde_json::from_value(json!({
            "range": {
                "start": { "line": 0, "character": 0 },
                "end": { "line": 1, "character": 0 }
            }
        }))
        .expect("kind is optional on the wire, defaulting to processing");
        assert_eq!(info.kind, LeanFileProgressKind::Processing);
    }

    #[test]
    fn test_file_progress_kind_fatal_error_round_trips_as_two() {
        let value = serde_json::to_value(LeanFileProgressKind::FatalError)
            .expect("serialize fatalError kind");
        assert_eq!(value, json!(2));
        let kind: LeanFileProgressKind =
            serde_json::from_value(json!(2)).expect("deserialize fatalError kind");
        assert_eq!(kind, LeanFileProgressKind::FatalError);
    }

    #[test]
    fn test_file_progress_kind_unknown_value_returns_error() {
        let result = serde_json::from_value::<LeanFileProgressKind>(json!(3));
        assert!(
            result.is_err(),
            "kind 3 is not a LeanFileProgressKind and must be rejected"
        );
    }

    /// Minimal LSP client side of an in-memory duplex connection: buffers
    /// bytes from the server and yields one framed JSON-RPC message at a time.
    struct FrameReader {
        reader: ReadHalf<DuplexStream>,
        buffer: Vec<u8>,
    }

    impl FrameReader {
        async fn next_message(&mut self) -> Value {
            loop {
                if let Some(message) = self.take_message() {
                    return message;
                }
                let mut chunk = [0_u8; 4096];
                let n = self
                    .reader
                    .read(&mut chunk)
                    .await
                    .expect("read from LSP server stream");
                assert!(
                    n > 0,
                    "LSP server closed the stream before the expected message arrived"
                );
                self.buffer.extend_from_slice(&chunk[..n]);
            }
        }

        fn take_message(&mut self) -> Option<Value> {
            let header_end = self.buffer.windows(4).position(|w| w == b"\r\n\r\n")?;
            let header =
                std::str::from_utf8(&self.buffer[..header_end]).expect("ASCII LSP frame header");
            let length: usize = header
                .lines()
                .find_map(|line| line.strip_prefix("Content-Length:"))
                .expect("Content-Length header in LSP frame")
                .trim()
                .parse()
                .expect("numeric Content-Length");
            let body_start = header_end + 4;
            if self.buffer.len() < body_start + length {
                return None;
            }
            let message = serde_json::from_slice(&self.buffer[body_start..body_start + length])
                .expect("valid JSON-RPC frame body");
            self.buffer.drain(..body_start + length);
            Some(message)
        }
    }

    async fn timeout_next(reader: &mut FrameReader) -> Value {
        tokio::time::timeout(Duration::from_secs(60), reader.next_message())
            .await
            .expect("timed out waiting for an LSP server message")
    }

    async fn write_message(writer: &mut WriteHalf<DuplexStream>, message: &Value) {
        let body = serde_json::to_string(message).expect("serialize JSON-RPC message");
        let frame = format!("Content-Length: {}\r\n\r\n{body}", body.len());
        writer
            .write_all(frame.as_bytes())
            .await
            .expect("write LSP frame to server");
    }

    /// End-to-end over the real server plumbing: didOpen must produce at
    /// least one `$/lean/fileProgress` with a non-empty processing range,
    /// per-declaration shrinking, and a terminal notification with empty
    /// ranges — in that order, all before diagnostics are published.
    #[tokio::test]
    async fn test_did_open_emits_file_progress_then_empty_terminal() {
        let (service, socket) = crate::build_service();
        let (client_io, server_io) = tokio::io::duplex(64 * 1024);
        let (server_read, server_write) = tokio::io::split(server_io);
        let server = tokio::spawn(async move {
            tower_lsp::Server::new(server_read, server_write, socket)
                .serve(service)
                .await;
        });

        let (client_read, mut client_write) = tokio::io::split(client_io);
        let mut reader = FrameReader {
            reader: client_read,
            buffer: Vec::new(),
        };

        write_message(
            &mut client_write,
            &json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": { "capabilities": {} }
            }),
        )
        .await;

        // Wait for the initialize response: tower-lsp only forwards
        // server-to-client notifications once the server is initialized.
        loop {
            let message = timeout_next(&mut reader).await;
            if message.get("id").and_then(Value::as_i64) == Some(1) {
                break;
            }
        }

        let uri = "file:///file_progress_test.lean";
        write_message(
            &mut client_write,
            &json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": { "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": "def one : Nat := 1\ndef two : Nat := 2\n"
                }}
            }),
        )
        .await;

        // check_document publishes diagnostics only after the terminal
        // fileProgress, so publishDiagnostics marks the end of the sequence.
        let mut progress_params: Vec<Value> = Vec::new();
        loop {
            let message = timeout_next(&mut reader).await;
            match message.get("method").and_then(Value::as_str) {
                Some("$/lean/fileProgress") => progress_params.push(message["params"].clone()),
                Some("textDocument/publishDiagnostics") => break,
                _ => {}
            }
        }
        server.abort();

        // Leading whole-file notification + one shrink (second decl) +
        // terminal empty notification.
        assert!(
            progress_params.len() >= 3,
            "expected leading, shrinking, and terminal fileProgress notifications, got: \
             {progress_params:?}"
        );

        for params in &progress_params {
            assert_eq!(
                params["textDocument"]["uri"],
                json!(uri),
                "fileProgress must target the opened document: {params:?}"
            );
            assert_eq!(
                params["textDocument"]["version"],
                json!(1),
                "fileProgress must carry the opened document version: {params:?}"
            );
        }

        let first = &progress_params[0];
        let first_ranges = first["processing"]
            .as_array()
            .expect("processing must be an array");
        assert!(
            !first_ranges.is_empty(),
            "leading fileProgress must carry a processing range: {first:?}"
        );
        assert_ne!(
            first_ranges[0]["range"]["start"], first_ranges[0]["range"]["end"],
            "leading processing range must be non-empty: {first:?}"
        );
        assert_eq!(
            first_ranges[0]["kind"],
            json!(1),
            "processing kind must serialize as 1 (LeanFileProgressKind.processing): {first:?}"
        );

        // The shrink notification for the second declaration starts on its
        // line (line 1), strictly after the leading whole-file range start.
        let shrunk_start_line = progress_params[1]["processing"][0]["range"]["start"]["line"]
            .as_u64()
            .expect("shrink notification must carry a range start line");
        assert!(
            shrunk_start_line >= 1,
            "per-declaration shrink must advance the processing start: {progress_params:?}"
        );

        // Exactly one empty-ranges notification, and it comes last.
        let empty_positions: Vec<usize> = progress_params
            .iter()
            .enumerate()
            .filter(|(_, params)| {
                params["processing"]
                    .as_array()
                    .is_some_and(|ranges| ranges.is_empty())
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(
            empty_positions,
            vec![progress_params.len() - 1],
            "the terminal empty-ranges fileProgress must come after every non-empty one: \
             {progress_params:?}"
        );
    }
}
