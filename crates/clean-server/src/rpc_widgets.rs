// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Widget RPC endpoint implementations for the Lean 4 infoview protocol.
//!
//! Implements `Lean.Widget.getWidgets` and `Lean.Widget.getWidgetSource`.
//! Protocol reference: <https://lean-lang.org/doc/api/Lean/Widget/UserWidget.html>

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// LSP-compatible types
// ---------------------------------------------------------------------------

/// Identifies a text document by its URI (mirrors LSP `TextDocumentIdentifier`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    pub uri: String,
}

/// A position inside a text document (0-indexed line and character).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Position {
    /// Line number (0-indexed).
    pub line: u32,
    /// Character offset (0-indexed, UTF-16 code units).
    pub character: u32,
}

// ---------------------------------------------------------------------------
// getWidgets
// ---------------------------------------------------------------------------

/// Parameters for `Lean.Widget.getWidgets`.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GetWidgetsParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
}

/// A single widget instance at a document position.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WidgetInstance {
    /// Widget module identifier.
    pub id: String,
    /// Human-readable display name.
    pub name: String,
    /// Content-addressable hash of the widget source.
    pub hash: String,
    /// Opaque props from the elaborator.
    pub props: serde_json::Value,
}

/// Response for `Lean.Widget.getWidgets`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GetWidgetsResponse {
    pub widgets: Vec<WidgetInstance>,
}

// ---------------------------------------------------------------------------
// getWidgetSource
// ---------------------------------------------------------------------------

/// Parameters for `Lean.Widget.getWidgetSource`.
#[derive(Debug, Clone, Deserialize)]
pub struct GetWidgetSourceParams {
    pub hash: String,
    pub position: Position,
}

/// Response for `Lean.Widget.getWidgetSource`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GetWidgetSourceResponse {
    /// Widget source (JavaScript/HTML), or `None` if the hash is unknown.
    pub source: Option<String>,
}

// ---------------------------------------------------------------------------
// Widget registry internals
// ---------------------------------------------------------------------------

/// Metadata parsed from a goal-state widget registration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WidgetRegistration {
    pub(crate) id: String,
    pub(crate) name: String,
    pub(crate) hash: String,
    pub(crate) line: u32,
    pub(crate) character: u32,
}

/// In-memory widget source store keyed by content hash.
#[derive(Debug, Clone, Default)]
pub(crate) struct WidgetSourceStore {
    sources: HashMap<String, String>,
}

impl WidgetSourceStore {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            sources: HashMap::new(),
        }
    }

    pub(crate) fn insert(&mut self, hash: String, source: String) {
        self.sources.insert(hash, source);
    }

    #[must_use]
    pub(crate) fn get(&self, hash: &str) -> Option<&str> {
        self.sources.get(hash).map(String::as_str)
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.sources.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Server-side widget state
// ---------------------------------------------------------------------------

/// Combined widget state held by the JSON-RPC server.
///
/// Bundles the content-addressed [`WidgetSourceStore`] with per-document
/// widget registration metadata. clean has no elaboration-time
/// `@[widget_module]` registration yet, so this store is populated explicitly
/// (e.g. by clients or future elaboration hooks) and queried by the widget
/// handlers. It is wrapped in a lock inside `ServerState` for shared,
/// interior-mutable access across requests.
#[derive(Debug, Clone, Default)]
pub(crate) struct WidgetState {
    /// JavaScript/HTML sources keyed by content hash.
    sources: WidgetSourceStore,
    /// Goal-state widget metadata keyed by document URI.
    metadata: HashMap<String, serde_json::Value>,
}

impl WidgetState {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a widget JavaScript/HTML source by its content hash.
    pub(crate) fn register_source(&mut self, hash: String, source: String) {
        self.sources.insert(hash, source);
    }

    /// Register (or replace) goal-state widget metadata for a document URI.
    pub(crate) fn register_document_widgets(&mut self, uri: String, metadata: serde_json::Value) {
        self.metadata.insert(uri, metadata);
    }

    /// Look up the goal-state widget metadata for a document URI, if any.
    #[must_use]
    pub(crate) fn document_metadata(&self, uri: &str) -> Option<&serde_json::Value> {
        self.metadata.get(uri)
    }

    /// Borrow the underlying source store.
    #[must_use]
    pub(crate) fn sources(&self) -> &WidgetSourceStore {
        &self.sources
    }

    /// Whether a widget instance with `id` is registered for `uri`.
    #[must_use]
    pub(crate) fn has_widget(&self, uri: &str, id: &str) -> bool {
        self.metadata
            .get(uri)
            .map(|meta| parse_widget_registrations(meta).iter().any(|r| r.id == id))
            .unwrap_or(false)
    }
}

// ---------------------------------------------------------------------------
// Goal-state metadata parsing
// ---------------------------------------------------------------------------

/// Parse widget registrations from goal-state metadata JSON.
///
/// Expects a `"widgets"` array with `id`, `name`, `hash` (required) and
/// `line`, `character` (defaulting to 0). Malformed entries are skipped.
pub(crate) fn parse_widget_registrations(metadata: &serde_json::Value) -> Vec<WidgetRegistration> {
    let Some(arr) = metadata.get("widgets").and_then(|v| v.as_array()) else {
        return Vec::new();
    };
    arr.iter()
        .filter_map(|e| {
            Some(WidgetRegistration {
                id: e.get("id")?.as_str()?.to_owned(),
                name: e.get("name")?.as_str()?.to_owned(),
                hash: e.get("hash")?.as_str()?.to_owned(),
                line: e.get("line").and_then(|v| v.as_u64()).unwrap_or(0) as u32,
                character: e.get("character").and_then(|v| v.as_u64()).unwrap_or(0) as u32,
            })
        })
        .collect()
}

/// Filter registrations to those in scope at `position` (defined before or at cursor).
pub(crate) fn widgets_at_position(
    registrations: &[WidgetRegistration],
    pos: Position,
) -> Vec<&WidgetRegistration> {
    registrations
        .iter()
        .filter(|w| w.line < pos.line || (w.line == pos.line && w.character <= pos.character))
        .collect()
}

// ---------------------------------------------------------------------------
// RPC handler entry points
// ---------------------------------------------------------------------------

/// Handle `Lean.Widget.getWidgets`.
///
/// Returns widget instances from goal-state metadata at the given position.
/// Returns an empty list when no metadata or widgets exist.
#[must_use]
pub fn handle_get_widgets(
    params: &GetWidgetsParams,
    metadata: Option<&serde_json::Value>,
) -> GetWidgetsResponse {
    let Some(meta) = metadata else {
        return GetWidgetsResponse {
            widgets: Vec::new(),
        };
    };
    let registrations = parse_widget_registrations(meta);
    let widgets = widgets_at_position(&registrations, params.position)
        .into_iter()
        .map(|r| WidgetInstance {
            id: r.id.clone(),
            name: r.name.clone(),
            hash: r.hash.clone(),
            props: serde_json::Value::Object(serde_json::Map::new()),
        })
        .collect();
    GetWidgetsResponse { widgets }
}

/// Handle `Lean.Widget.getWidgetSource`.
///
/// Returns `source: None` when the hash is unknown (graceful degradation).
#[must_use]
pub(crate) fn handle_get_widget_source(
    params: &GetWidgetSourceParams,
    store: &WidgetSourceStore,
) -> GetWidgetSourceResponse {
    GetWidgetSourceResponse {
        source: store.get(&params.hash).map(str::to_owned),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn pos(line: u32, character: u32) -> Position {
        Position { line, character }
    }

    fn tdi(uri: &str) -> TextDocumentIdentifier {
        TextDocumentIdentifier {
            uri: uri.to_owned(),
        }
    }

    fn reg(id: &str, hash: &str, line: u32, character: u32) -> WidgetRegistration {
        WidgetRegistration {
            id: id.to_owned(),
            name: id.to_owned(),
            hash: hash.to_owned(),
            line,
            character,
        }
    }

    fn gw_params(line: u32, character: u32) -> GetWidgetsParams {
        GetWidgetsParams {
            text_document: tdi("file:///tmp/Test.lean"),
            position: pos(line, character),
        }
    }

    // -- LSP types serde ----------------------------------------------------

    #[test]
    fn test_text_document_identifier_roundtrip() {
        let orig = tdi("file:///tmp/Test.lean");
        let back: TextDocumentIdentifier =
            serde_json::from_str(&serde_json::to_string(&orig).unwrap()).unwrap();
        assert_eq!(orig, back);
    }

    #[test]
    fn test_position_default_and_roundtrip() {
        let def = Position::default();
        assert_eq!(def.line, 0);
        assert_eq!(def.character, 0);
        let p = pos(42, 7);
        let back: Position = serde_json::from_str(&serde_json::to_string(&p).unwrap()).unwrap();
        assert_eq!(p, back);
    }

    // -- Params deserialization ---------------------------------------------

    #[test]
    fn test_get_widgets_params_deserialize() {
        let json =
            r#"{"textDocument":{"uri":"file:///a.lean"},"position":{"line":10,"character":5}}"#;
        let p: GetWidgetsParams = serde_json::from_str(json).unwrap();
        assert_eq!(p.text_document.uri, "file:///a.lean");
        assert_eq!(p.position, pos(10, 5));
    }

    #[test]
    fn test_get_widget_source_params_deserialize() {
        let json = r#"{"hash":"deadbeef","position":{"line":0,"character":0}}"#;
        let p: GetWidgetSourceParams = serde_json::from_str(json).unwrap();
        assert_eq!(p.hash, "deadbeef");
    }

    // -- WidgetInstance / response serde ------------------------------------

    #[test]
    fn test_widget_instance_roundtrip() {
        let wi = WidgetInstance {
            id: "w".to_owned(),
            name: "W".to_owned(),
            hash: "h".to_owned(),
            props: serde_json::json!({"k": 1}),
        };
        let back: WidgetInstance =
            serde_json::from_str(&serde_json::to_string(&wi).unwrap()).unwrap();
        assert_eq!(wi, back);
    }

    #[test]
    fn test_get_widgets_response_serde() {
        let empty = GetWidgetsResponse { widgets: vec![] };
        assert!(serde_json::to_string(&empty)
            .unwrap()
            .contains("\"widgets\":[]"));

        let one = GetWidgetsResponse {
            widgets: vec![WidgetInstance {
                id: "w1".to_owned(),
                name: "W1".to_owned(),
                hash: "h1".to_owned(),
                props: serde_json::Value::Null,
            }],
        };
        let v = serde_json::to_value(&one).unwrap();
        assert_eq!(v["widgets"][0]["id"], "w1");
    }

    #[test]
    fn test_get_widget_source_response_serde() {
        let none_resp = GetWidgetSourceResponse { source: None };
        assert!(serde_json::to_string(&none_resp).unwrap().contains("null"));
        let some_resp = GetWidgetSourceResponse {
            source: Some("src".to_owned()),
        };
        assert_eq!(serde_json::to_value(&some_resp).unwrap()["source"], "src");
    }

    // -- WidgetSourceStore --------------------------------------------------

    #[test]
    fn test_source_store_operations() {
        let mut store = WidgetSourceStore::new();
        assert!(store.is_empty());
        assert_eq!(store.get("x"), None);

        store.insert("h1".to_owned(), "v1".to_owned());
        assert_eq!(store.len(), 1);
        assert_eq!(store.get("h1"), Some("v1"));
        assert_eq!(store.get("h2"), None);

        // Overwrite
        store.insert("h1".to_owned(), "v2".to_owned());
        assert_eq!(store.len(), 1);
        assert_eq!(store.get("h1"), Some("v2"));
    }

    // -- parse_widget_registrations -----------------------------------------

    #[test]
    fn test_parse_registrations_missing_or_empty() {
        assert!(parse_widget_registrations(&serde_json::json!({"goals": []})).is_empty());
        assert!(parse_widget_registrations(&serde_json::json!({"widgets": []})).is_empty());
    }

    #[test]
    fn test_parse_registrations_valid_entry() {
        let meta = serde_json::json!({"widgets": [{
            "id": "G", "name": "Goal", "hash": "abc", "line": 5, "character": 10
        }]});
        let regs = parse_widget_registrations(&meta);
        assert_eq!(regs.len(), 1);
        assert_eq!(
            regs[0],
            WidgetRegistration {
                id: "G".to_owned(),
                name: "Goal".to_owned(),
                hash: "abc".to_owned(),
                line: 5,
                character: 10,
            }
        );
    }

    #[test]
    fn test_parse_registrations_skips_malformed() {
        let meta = serde_json::json!({"widgets": [
            {"id": "w1", "name": "W1"},
            {"id": "w2", "name": "W2", "hash": "h2"}
        ]});
        let regs = parse_widget_registrations(&meta);
        assert_eq!(regs.len(), 1);
        assert_eq!(regs[0].id, "w2");
        // line/character default to 0
        assert_eq!(regs[0].line, 0);
    }

    #[test]
    fn test_parse_registrations_multiple() {
        let meta = serde_json::json!({"widgets": [
            {"id": "a", "name": "A", "hash": "h1", "line": 1, "character": 0},
            {"id": "b", "name": "B", "hash": "h2", "line": 5, "character": 3},
            {"id": "c", "name": "C", "hash": "h3", "line": 10, "character": 0}
        ]});
        assert_eq!(parse_widget_registrations(&meta).len(), 3);
    }

    // -- widgets_at_position ------------------------------------------------

    #[test]
    fn test_widgets_at_position_visibility() {
        let regs = vec![
            reg("w1", "h1", 0, 0),
            reg("w2", "h2", 5, 10),
            reg("w3", "h3", 10, 0),
        ];

        // All visible at line 20
        assert_eq!(widgets_at_position(&regs, pos(20, 0)).len(), 3);
        // Only w1 visible at line 3
        let m = widgets_at_position(&regs, pos(3, 0));
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].id, "w1");
        // None visible before line 0 (impossible, but line 0 char 0 sees w1)
        assert_eq!(widgets_at_position(&regs, pos(0, 0)).len(), 1);
    }

    #[test]
    fn test_widgets_at_position_same_line_character_boundary() {
        let regs = vec![reg("w1", "h1", 5, 10)];
        // Before character: not visible
        assert!(widgets_at_position(&regs, pos(5, 5)).is_empty());
        // At character: visible
        assert_eq!(widgets_at_position(&regs, pos(5, 10)).len(), 1);
        // After character: visible
        assert_eq!(widgets_at_position(&regs, pos(5, 15)).len(), 1);
    }

    #[test]
    fn test_widgets_at_position_empty_registrations() {
        assert!(widgets_at_position(&[], pos(10, 0)).is_empty());
    }

    // -- handle_get_widgets -------------------------------------------------

    #[test]
    fn test_handle_get_widgets_no_metadata() {
        let resp = handle_get_widgets(&gw_params(0, 0), None);
        assert!(resp.widgets.is_empty());
    }

    #[test]
    fn test_handle_get_widgets_with_metadata() {
        let meta = serde_json::json!({"widgets": [{
            "id": "G", "name": "Goal", "hash": "abc", "line": 0, "character": 0
        }]});
        let resp = handle_get_widgets(&gw_params(10, 0), Some(&meta));
        assert_eq!(resp.widgets.len(), 1);
        assert_eq!(resp.widgets[0].id, "G");
        assert_eq!(resp.widgets[0].hash, "abc");
        assert!(resp.widgets[0].props.is_object());
    }

    #[test]
    fn test_handle_get_widgets_filters_by_position() {
        let meta = serde_json::json!({"widgets": [
            {"id": "early", "name": "E", "hash": "h1", "line": 1, "character": 0},
            {"id": "late", "name": "L", "hash": "h2", "line": 100, "character": 0}
        ]});
        let resp = handle_get_widgets(&gw_params(50, 0), Some(&meta));
        assert_eq!(resp.widgets.len(), 1);
        assert_eq!(resp.widgets[0].id, "early");
    }

    // -- handle_get_widget_source -------------------------------------------

    #[test]
    fn test_handle_get_widget_source_found_and_missing() {
        let mut store = WidgetSourceStore::new();
        store.insert("abc".to_owned(), "<div>w</div>".to_owned());

        let found = handle_get_widget_source(
            &GetWidgetSourceParams {
                hash: "abc".to_owned(),
                position: Position::default(),
            },
            &store,
        );
        assert_eq!(found.source.as_deref(), Some("<div>w</div>"));

        let missing = handle_get_widget_source(
            &GetWidgetSourceParams {
                hash: "nope".to_owned(),
                position: Position::default(),
            },
            &store,
        );
        assert_eq!(missing.source, None);

        // Empty store
        let empty_store = WidgetSourceStore::new();
        let empty = handle_get_widget_source(
            &GetWidgetSourceParams {
                hash: "x".to_owned(),
                position: pos(5, 3),
            },
            &empty_store,
        );
        assert_eq!(empty.source, None);
    }
}
