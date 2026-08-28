// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wire-level regression: `textDocument/hover` must answer where a user hovers.
//!
//! Hover was advertised in `initialize`, in the crate docs and in a
//! `Stability::Usable` CLI descriptor, and it was dead. Measured at the wire on
//! `d33c59dd7` by an exhaustive grid sweep over a 16-line file: non-`null` at
//! **28 of 385** cursor positions — and those 28 were exactly the bytes of the
//! `def` / `theorem` / `structure` KEYWORDS of declarations that elaborated.
//! Every identifier, type, binder and body position answered `null`.
//!
//! Not one of `clean-lsp`'s ~380 tests could see it. They call backend methods
//! directly and assert on structure; the one hover test in the suite queried
//! `decl.start` — a keyword byte — and passed. This module sweeps the SAME grid
//! over the real service, so the measurement that found the defect is the
//! measurement that guards it.
//!
//! Non-vacuity is enforced, not assumed: the sweep fails if the fixture
//! produces no document symbols (nothing elaborated, so every `null` would be
//! honest), and the count assertion is stated as a floor far above the
//! keyword-only ceiling the defect imposed.

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};
    use std::time::Duration;
    use tokio::io::{AsyncReadExt, AsyncWriteExt, DuplexStream, ReadHalf, WriteHalf};

    /// Import-free so the sweep runs against the prelude floor rather than an
    /// `.olean` closure load. `uses_double` calls `double` so the sweep can
    /// check that hover reports the type of the identifier under the cursor,
    /// not the enclosing declaration's; `broken` fails to elaborate so the
    /// sweep also covers a declaration with no type of its own.
    const DOC: &str = concat!(
        "def double (n : Nat) : Nat := n + n\n",
        "def uses_double (n : Nat) : Nat := double n\n",
        "\n",
        "theorem broken : 1 = 2 := rfl\n",
    );

    /// Total cursor positions in `DOC` — every (line, character) with
    /// `character` in `0..=line.len()`, the grid the original measurement used.
    fn grid_positions() -> Vec<(u32, u32)> {
        DOC.split('\n')
            .enumerate()
            .flat_map(|(line, text)| {
                (0..=text.chars().count()).map(move |ch| (line as u32, ch as u32))
            })
            .collect()
    }

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
        tokio::time::timeout(Duration::from_secs(120), reader.next_message())
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

    /// Send a request and return its `result`, answering any server->client
    /// request that arrives first so the connection cannot deadlock.
    async fn request(
        writer: &mut WriteHalf<DuplexStream>,
        reader: &mut FrameReader,
        id: i64,
        method: &str,
        params: Value,
    ) -> Value {
        write_message(
            writer,
            &json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}),
        )
        .await;
        loop {
            let message = timeout_next(reader).await;
            if message.get("id").and_then(Value::as_i64) == Some(id)
                && message.get("method").is_none()
            {
                return message.get("result").cloned().unwrap_or(Value::Null);
            }
            if let (Some(server_id), Some(_)) = (message.get("id"), message.get("method")) {
                write_message(
                    writer,
                    &json!({"jsonrpc": "2.0", "id": server_id, "result": Value::Null}),
                )
                .await;
            }
        }
    }

    fn hover_text(result: &Value) -> Option<&str> {
        result.get("contents")?.get("value")?.as_str()
    }

    /// Grid-sweep `textDocument/hover` over the real server.
    ///
    /// The floor of 60 is a ratchet, not a target: the defect capped the sweep
    /// at the command-keyword bytes (7 here — `def`, `def`, and `theorem`,
    /// minus the failing declaration's), so any regression toward
    /// keyword-only spans fails this by an order of magnitude.
    #[tokio::test]
    async fn test_wire_hover_answers_across_the_declaration_not_only_its_keyword() {
        let (service, socket) = crate::build_service();
        let (client_io, server_io) = tokio::io::duplex(256 * 1024);
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

        request(
            &mut client_write,
            &mut reader,
            1,
            "initialize",
            json!({"capabilities": {}}),
        )
        .await;

        let uri = "file:///hover_wire.lean";
        write_message(
            &mut client_write,
            &json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": { "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": DOC
                }}
            }),
        )
        .await;

        // Elaboration is a background task; hover before it commits answers
        // from an empty snapshot. Wait for the terminal (empty-ranges)
        // fileProgress AND the elaboration diagnostics that follow it.
        let mut elaboration_finished = false;
        loop {
            let message = timeout_next(&mut reader).await;
            match message.get("method").and_then(Value::as_str) {
                Some("textDocument/publishDiagnostics") if elaboration_finished => break,
                Some("$/lean/fileProgress")
                    if message["params"]["processing"]
                        .as_array()
                        .is_some_and(|ranges| ranges.is_empty()) =>
                {
                    elaboration_finished = true;
                }
                _ => {}
            }
        }

        // Non-vacuity: if nothing elaborated, every `null` below would be
        // honest and the sweep would prove nothing.
        let symbols = request(
            &mut client_write,
            &mut reader,
            2,
            "textDocument/documentSymbol",
            json!({"textDocument": {"uri": uri}}),
        )
        .await;
        let symbol_names: Vec<String> = symbols
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|s| s["name"].as_str().map(str::to_string))
            .collect();
        for expected in ["double", "uses_double"] {
            assert!(
                symbol_names.iter().any(|name| name == expected),
                "fixture must elaborate `{expected}` or the hover sweep is vacuous; \
                 got {symbol_names:?}"
            );
        }

        let positions = grid_positions();
        let mut answered = Vec::new();
        let mut by_position = std::collections::HashMap::new();
        for (index, (line, character)) in positions.iter().enumerate() {
            let result = request(
                &mut client_write,
                &mut reader,
                100 + index as i64,
                "textDocument/hover",
                json!({
                    "textDocument": {"uri": uri},
                    "position": {"line": line, "character": character}
                }),
            )
            .await;
            if !result.is_null() {
                answered.push((*line, *character));
            }
            by_position.insert((*line, *character), result);
        }
        server.abort();

        assert!(
            answered.len() >= 60,
            "hover answered at only {} of {} cursor positions — the keyword-only \
             declaration span is back. Answered: {answered:?}",
            answered.len(),
            positions.len()
        );

        // The identifier under the cursor wins over the enclosing declaration:
        // `double` inside `uses_double`'s body reports `double`'s type.
        let call_site = by_position
            .get(&(1, 37))
            .expect("swept position 1:37 (`double` in `uses_double`)");
        let call_site_text =
            hover_text(call_site).unwrap_or_else(|| panic!("1:37 answered {call_site}"));
        assert!(
            call_site_text.contains("double : "),
            "hover on the call site should report `double`'s signature, got {call_site_text:?}"
        );
        assert!(
            !call_site_text.contains("uses_double"),
            "hover on the call site reported the ENCLOSING declaration instead of \
             the identifier under the cursor, got {call_site_text:?}"
        );
        assert_eq!(
            call_site["range"],
            json!({"start": {"line": 1, "character": 35},
                   "end": {"line": 1, "character": 41}}),
            "hover on an identifier should range over the identifier"
        );

        // A position with no identifier and outside the keyword — the class
        // that answered `null` for every declaration before the repair.
        let ascription = by_position
            .get(&(0, 21))
            .expect("swept position 0:21 (the `:` of `double`'s result type)");
        let ascription_text =
            hover_text(ascription).unwrap_or_else(|| panic!("0:21 answered {ascription}"));
        assert!(
            ascription_text.contains("double : "),
            "hover inside the declaration but outside its keyword should report the \
             declaration, got {ascription_text:?}"
        );

        // Whitespace between declarations belongs to no declaration.
        assert!(
            by_position.get(&(2, 0)).is_some_and(Value::is_null),
            "the blank line between declarations must not hover"
        );
    }
}
