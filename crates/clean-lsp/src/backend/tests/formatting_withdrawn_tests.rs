// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The formatter is withdrawn (plan item `devsurface-lsp-formatter-withdraw`).
//!
//! On `textDocument/formatting`, `rangeFormatting` and `onTypeFormatting`,
//! clean-lsp used to trim trailing whitespace from every line, and a line can
//! end inside a string literal. For `def s := "a  `, a line break and `b"`,
//! pinned Lean (v4.30.0-rc2) evaluates `s.length` to 5, and to 3 once the two
//! spaces are trimmed. Pinned Lean advertises none of the three capabilities.
//!
//! The contract pinned here: `initialize` carries none of the three keys, and
//! each request is still answered, with `null`, so applying the answer leaves
//! the document's bytes as they were.

use crate::backend::CleanBackend;
use crate::document::Document;
use std::cmp::Reverse;
use tower_lsp::lsp_types::{
    DocumentFormattingParams, DocumentOnTypeFormattingParams, DocumentRangeFormattingParams,
    FormattingOptions, InitializeParams, Position, Range, TextDocumentIdentifier,
    TextDocumentPositionParams, TextEdit, Url, WorkDoneProgressParams,
};
use tower_lsp::{LanguageServer, LspService};

/// The first line ends with two spaces inside the string literal.
const MULTILINE_STRING: &str = "def s := \"a  \nb\"";

const URI: &str = "file:///formatting-withdrawn.lean";

/// The capability keys the withdrawn formatter put in the `initialize` result.
const WITHDRAWN_CAPABILITY_KEYS: &[&str] = &[
    "documentFormattingProvider",
    "documentRangeFormattingProvider",
    "documentOnTypeFormattingProvider",
];

/// The on-type triggers the withdrawn capability registered: its
/// `firstTriggerCharacter`. It registered no `moreTriggerCharacter`.
const OLD_ON_TYPE_TRIGGER_CHARACTERS: &[&str] = &["\n"];

fn uri() -> Url {
    Url::parse(URI).expect("the test URI should parse")
}

fn open_document(backend: &CleanBackend, text: &str) {
    backend.documents.insert(
        uri(),
        Document::new(uri(), 1, text.to_string(), "lean".to_string()),
    );
}

/// Apply `edits` to `text` as a client does: every range is read against the
/// text before any edit, and a position past the end of the text is clamped
/// to it (`Document::position_to_offset`).
fn apply_edits(text: &str, edits: &[TextEdit]) -> String {
    let doc = Document::new(uri(), 0, text.to_string(), "lean".to_string());
    let mut spans: Vec<(usize, usize, &str)> = edits
        .iter()
        .map(|edit| {
            (
                doc.position_to_offset(edit.range.start),
                doc.position_to_offset(edit.range.end),
                edit.new_text.as_str(),
            )
        })
        .collect();
    spans.sort_by_key(|&(start, _, _)| Reverse(start));
    let mut edited = text.to_string();
    for (start, end, new_text) in spans {
        edited.replace_range(start..end, new_text);
    }
    edited
}

#[tokio::test]
async fn test_formatting_trailing_spaces_inside_multiline_string_leave_bytes_unchanged() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    open_document(backend, MULTILINE_STRING);

    let response = LanguageServer::formatting(
        backend,
        DocumentFormattingParams {
            text_document: TextDocumentIdentifier { uri: uri() },
            options: FormattingOptions::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("textDocument/formatting should be answered, not refused");

    assert_eq!(
        apply_edits(MULTILINE_STRING, response.as_deref().unwrap_or_default()),
        MULTILINE_STRING,
        "formatting must not change the bytes of the document"
    );
    assert!(
        response.is_none(),
        "formatting should answer null (no edits), got {response:?}"
    );
}

#[tokio::test]
async fn test_range_formatting_trailing_spaces_inside_multiline_string_leave_bytes_unchanged() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    open_document(backend, MULTILINE_STRING);

    // The whole document, its first line with the line break, and the two
    // trailing spaces alone.
    let ranges = [
        Range::new(Position::new(0, 0), Position::new(1, 2)),
        Range::new(Position::new(0, 0), Position::new(1, 0)),
        Range::new(Position::new(0, 11), Position::new(0, 13)),
    ];
    for range in ranges {
        let response = LanguageServer::range_formatting(
            backend,
            DocumentRangeFormattingParams {
                text_document: TextDocumentIdentifier { uri: uri() },
                range,
                options: FormattingOptions::default(),
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        )
        .await
        .expect("textDocument/rangeFormatting should be answered, not refused");

        assert_eq!(
            apply_edits(MULTILINE_STRING, response.as_deref().unwrap_or_default()),
            MULTILINE_STRING,
            "range formatting over {range:?} must not change the bytes of the document"
        );
        assert!(
            response.is_none(),
            "range formatting over {range:?} should answer null (no edits), got {response:?}"
        );
    }
}

#[tokio::test]
async fn test_on_type_formatting_newline_after_string_spaces_leaves_bytes_unchanged() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    open_document(backend, MULTILINE_STRING);

    // The cursor right after the line break that ends `def s := "a  `.
    let after_line_break = Position::new(1, 0);
    for &ch in OLD_ON_TYPE_TRIGGER_CHARACTERS {
        let response = LanguageServer::on_type_formatting(
            backend,
            DocumentOnTypeFormattingParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: uri() },
                    position: after_line_break,
                },
                ch: ch.to_string(),
                options: FormattingOptions::default(),
            },
        )
        .await
        .expect("textDocument/onTypeFormatting should be answered, not refused");

        assert_eq!(
            apply_edits(MULTILINE_STRING, response.as_deref().unwrap_or_default()),
            MULTILINE_STRING,
            "on-type formatting after {ch:?} must not change the bytes of the document"
        );
        assert!(
            response.is_none(),
            "on-type formatting after {ch:?} should answer null (no edits), got {response:?}"
        );
    }
}

#[tokio::test]
async fn test_initialize_default_params_carries_no_formatting_capability_key() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");
    let wire = serde_json::to_value(&result).expect("the initialize result should serialize");
    let capabilities = wire
        .get("capabilities")
        .and_then(serde_json::Value::as_object)
        .expect("the initialize result should carry a capabilities object");

    // Control: this is the object clients read, so an absent key is absent on
    // the wire and not an artifact of reading the wrong place.
    assert!(
        capabilities.contains_key("hoverProvider"),
        "the serialized capabilities should carry hoverProvider: {capabilities:?}"
    );
    // A key present with `null` fails too.
    for &key in WITHDRAWN_CAPABILITY_KEYS {
        assert!(
            !capabilities.contains_key(key),
            "initialize must not carry `{key}`; pinned Lean advertises no formatter. Got {:?}",
            capabilities.get(key)
        );
    }
}
