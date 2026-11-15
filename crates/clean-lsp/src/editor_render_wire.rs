// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wire-level regression: no editor surface may ship Rust `Debug` output.
//!
//! Every user-visible string an editor renders — infoview goals
//! (`$/lean/plainGoal`) and problems-panel diagnostics
//! (`textDocument/publishDiagnostics`) — is produced by the elaborator's
//! goal/error formatters. Until 2026-08-26 those formatters used `{:?}` on
//! kernel `Expr`s, so the infoview for
//!
//! ```text
//! theorem leftover : (1 : Nat) + 1 = 2 := by
//!   skip
//! ```
//!
//! rendered as `⊢ App(App(App(Const(Name { depth: 1, suffix: ["Eq"],
//! lean4_hash: dfbff609f865258f }, …` and a failing `rfl` produced a
//! 1000+ character `App(App(Const(…` string in the problems panel.
//!
//! `clean-lsp` has hundreds of tests and not one of them could observe this:
//! they call backend methods directly and assert on structure, never on the
//! bytes that cross the wire. This module drives the REAL service over
//! `tokio::io::duplex` (the pattern proven in [`crate::file_progress`]) and
//! asserts on the rendered strings themselves.
//!
//! The assertion is deliberately a *ban list of Rust `Debug` shapes* rather
//! than an expected-output match: a ban list cannot go vacuous the way a
//! golden string can, and it stays true for every future improvement to the
//! pretty-printer. Non-vacuity is enforced separately — the test fails if the
//! document produces no diagnostics or no goal, so a regression that simply
//! stops answering cannot masquerade as a pass.

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};
    use std::time::Duration;
    use tokio::io::{AsyncReadExt, AsyncWriteExt, DuplexStream, ReadHalf, WriteHalf};

    /// A document exercising the two formatters every editor surface funnels
    /// through: the goal renderer (`leftover`, whose `skip` leaves a goal for
    /// both the infoview and an unsolved-goals diagnostic) and the tactic
    /// error renderer (`broken`, whose `rfl` reports a type mismatch).
    const DOC: &str = concat!(
        "theorem leftover : (1 : Nat) + 1 = 2 := by\n",
        "  skip\n",
        "\n",
        "theorem broken : (1 : Nat) + 1 = 3 := by\n",
        "  rfl\n",
    );

    /// Rust `Debug` shapes that must never reach an editor.
    ///
    /// `lean4_hash` is the sharpest of these — it is a field of
    /// `clean_kernel::Name`'s derived `Debug` and has no other way to appear
    /// in a rendered string, so it cannot be produced by a legitimate
    /// pretty-printer.
    const BANNED: &[&str] = &[
        "lean4_hash",
        "Const(Name {",
        "App(App(",
        "Succ(Zero)",
        "Lit(Nat(Small",
        "Nat(Small(",
        "Small(",
        "BinderData {",
        "FVarId(",
    ];

    fn assert_no_debug_render(label: &str, text: &str) {
        for needle in BANNED {
            assert!(
                !text.contains(needle),
                "{label} shipped Rust Debug output to the editor: found {needle:?} in\n{text}"
            );
        }
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

    /// End-to-end over the real server plumbing: open a document whose
    /// declarations both fail, drain every published diagnostic, then ask for
    /// the infoview goal. Neither surface may contain a Rust `Debug` shape,
    /// and both must be non-empty.
    #[tokio::test]
    async fn test_wire_goals_and_diagnostics_carry_no_rust_debug_render() {
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
        loop {
            let message = timeout_next(&mut reader).await;
            if message.get("id").and_then(Value::as_i64) == Some(1) {
                break;
            }
        }

        let uri = "file:///editor_render_wire.lean";
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

        // The server publishes an empty parse-phase diagnostics set first,
        // then the terminal (empty-ranges) `$/lean/fileProgress`, and only
        // then the FULL elaboration diagnostics. Draining to the terminal
        // progress alone therefore collects nothing — keep reading until the
        // post-terminal publish arrives.
        let mut diagnostic_messages: Vec<String> = Vec::new();
        let mut elaboration_finished = false;
        loop {
            let message = timeout_next(&mut reader).await;
            match message.get("method").and_then(Value::as_str) {
                Some("textDocument/publishDiagnostics") => {
                    for diagnostic in message["params"]["diagnostics"]
                        .as_array()
                        .into_iter()
                        .flatten()
                    {
                        if let Some(text) = diagnostic["message"].as_str() {
                            diagnostic_messages.push(text.to_string());
                        }
                    }
                    if elaboration_finished {
                        break;
                    }
                }
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

        // The infoview goal for `leftover`'s `skip` (line 1, inside the
        // tactic block).
        write_message(
            &mut client_write,
            &json!({
                "jsonrpc": "2.0",
                "id": 2,
                "method": "$/lean/plainGoal",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 1, "character": 3 }
                }
            }),
        )
        .await;
        let goal_response = loop {
            let message = timeout_next(&mut reader).await;
            if message.get("id").and_then(Value::as_i64) == Some(2) {
                break message;
            }
        };
        write_message(
            &mut client_write,
            &json!({
                "jsonrpc": "2.0",
                "id": 3,
                "method": "$/lean/plainGoal",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 0, "character": 0 }
                }
            }),
        )
        .await;
        let outside_response = loop {
            let message = timeout_next(&mut reader).await;
            if message.get("id").and_then(Value::as_i64) == Some(3) {
                break message;
            }
        };
        server.abort();

        assert!(
            outside_response.get("result").is_some_and(Value::is_null),
            "plainGoal outside a tactic snapshot must reply with null: {outside_response}"
        );

        let goals: Vec<String> = goal_response["result"]["goals"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|g| g.as_str().map(str::to_string))
            .collect();

        // Non-vacuity: a surface that answers nothing must not pass.
        assert!(
            !goals.is_empty(),
            "$/lean/plainGoal returned no goal for `skip`; the ban-list assertion \
             below would be vacuous. Response: {goal_response}"
        );
        let rendered = goal_response["result"]["rendered"]
            .as_str()
            .expect("plainGoal must provide Lean's Markdown rendered field");
        assert!(rendered.starts_with("```lean\n") && rendered.ends_with("\n```"));
        assert!(
            !diagnostic_messages.is_empty(),
            "the document's two failing declarations published no diagnostics; \
             the ban-list assertion below would be vacuous"
        );

        for goal in &goals {
            assert_no_debug_render("$/lean/plainGoal", goal);
            assert!(
                rendered.contains(goal),
                "rendered reply dropped the live goal"
            );
        }
        assert_no_debug_render("$/lean/plainGoal rendered", rendered);
        for message in &diagnostic_messages {
            assert_no_debug_render("textDocument/publishDiagnostics", message);
        }
    }
}
