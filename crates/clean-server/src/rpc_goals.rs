// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal-related RPC endpoints for Lean 4 editor infoview parity.
//!
//! - `Lean.Widget.getInteractiveGoals` — structured goal info at a position
//! - `Lean.Widget.getInteractiveDiagnostics` — diagnostics with interactive components
//! - `getPlainGoal` — plain-text rendering of goals (convenience endpoint)
//!
//! Protocol reference: Lean.Widget.InteractiveGoal
//! <https://lean-lang.org/doc/api/Lean/Widget/InteractiveGoal.html>
//!
//! Part of #1245

use serde::{Deserialize, Serialize};

use super::{RequestId, Response, RpcError};

// ============================================================================
// LSP Position Types (local to clean-server, no tower-lsp dependency)
// ============================================================================

/// Text document identifier (URI only).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    pub uri: String,
}

/// Zero-indexed line/character position within a text document.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

/// Zero-indexed range within a text document.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

// ============================================================================
// Interactive Goal Types (shared home: clean_elab::interactive_goals)
// ============================================================================

// The interactive goal payloads and their plain-text rendering live in
// `clean_elab::interactive_goals` — the single shared home used by both this
// TCP/WebSocket JSON-RPC channel and the LSP `$/lean/rpc/call` channel
// (`clean-lsp`), so the two protocols serve one data shape. Re-exported here
// to keep existing `crate::rpc_goals::*` paths stable.
pub use clean_elab::interactive_goals::{
    render_goal_plain, render_goals_plain, InteractiveGoal, InteractiveGoals,
    InteractiveHypothesisBundle,
};

// ============================================================================
// Interactive Diagnostics Types
// ============================================================================

/// Severity level matching LSP `DiagnosticSeverity`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

/// A diagnostic with optional interactive components.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InteractiveDiagnostic {
    pub range: Range,
    pub severity: DiagnosticSeverity,
    pub message: String,
}

/// Response for `Lean.Widget.getInteractiveDiagnostics`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InteractiveDiagnostics {
    pub diagnostics: Vec<InteractiveDiagnostic>,
}

// ============================================================================
// Request Parameter Types
// ============================================================================

/// Parameters for `Lean.Widget.getInteractiveGoals` and `getPlainGoal`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PlainGoalParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
}

/// Parameters for `Lean.Widget.getInteractiveDiagnostics`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GetInteractiveDiagnosticsParams {
    pub text_document: TextDocumentIdentifier,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub line_range: Option<(u32, u32)>,
}

// ============================================================================
// RPC Handlers
// ============================================================================

/// Handle `Lean.Widget.getInteractiveGoals`.
///
/// Returns empty goals until the elaborator records per-position tactic state.
pub(crate) async fn handle_get_interactive_goals(
    _state: &crate::handlers::ServerState,
    id: RequestId,
    _params: PlainGoalParams,
) -> Response {
    let result = InteractiveGoals { goals: vec![] };
    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle `Lean.Widget.getInteractiveDiagnostics`.
///
/// Returns empty diagnostics until the elaborator produces interactive payloads.
pub(crate) async fn handle_get_interactive_diagnostics(
    _state: &crate::handlers::ServerState,
    id: RequestId,
    _params: GetInteractiveDiagnosticsParams,
) -> Response {
    let result = InteractiveDiagnostics {
        diagnostics: vec![],
    };
    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle `getPlainGoal`.
///
/// Convenience endpoint returning goals as a single plain-text string.
pub(crate) async fn handle_get_plain_goal(
    _state: &crate::handlers::ServerState,
    id: RequestId,
    _params: PlainGoalParams,
) -> Response {
    let goals = InteractiveGoals { goals: vec![] };
    let rendered = render_goals_plain(&goals);
    Response::success_typed(id.clone(), &rendered)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_goal(hyps: Vec<(&str, &str)>, target: &str) -> InteractiveGoal {
        InteractiveGoal {
            hyps: hyps
                .into_iter()
                .map(|(n, t)| InteractiveHypothesisBundle {
                    names: n.split_whitespace().map(String::from).collect(),
                    type_: t.into(),
                    is_instance: false,
                    is_inserted: false,
                })
                .collect(),
            type_: target.into(),
            goal_prefix: "\u{22a2}".into(),
            username: None,
            is_converted: false,
        }
    }

    // -- Serde round-trip tests ------------------------------------------------

    #[test]
    fn test_plain_goal_params_camel_case() {
        let json =
            r#"{"textDocument":{"uri":"file:///t.lean"},"position":{"line":3,"character":12}}"#;
        let p: PlainGoalParams = serde_json::from_str(json).unwrap();
        assert_eq!(p.text_document.uri, "file:///t.lean");
        assert_eq!(
            p.position,
            Position {
                line: 3,
                character: 12
            }
        );
    }

    #[test]
    fn test_interactive_goal_serde_roundtrip() {
        let goal = make_goal(vec![("a b", "Nat"), ("h", "a = b")], "b = a");
        let json = serde_json::to_string(&goal).unwrap();
        let parsed: InteractiveGoal = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.hyps.len(), 2);
        assert_eq!(parsed.hyps[0].names, ["a", "b"]);
        assert_eq!(parsed.type_, "b = a");
    }

    #[test]
    fn test_interactive_goal_default_prefix() {
        let json = r#"{"hyps":[],"type":"True"}"#;
        let goal: InteractiveGoal = serde_json::from_str(json).unwrap();
        assert_eq!(goal.goal_prefix, "\u{22a2}");
        assert!(!goal.is_converted);
        assert!(goal.username.is_none());
    }

    #[test]
    fn test_interactive_goal_case_prefix() {
        let json = r#"{"hyps":[],"type":"P n","goalPrefix":"case succ","username":"succ","isConverted":false}"#;
        let goal: InteractiveGoal = serde_json::from_str(json).unwrap();
        assert_eq!(goal.goal_prefix, "case succ");
        assert_eq!(goal.username.as_deref(), Some("succ"));
    }

    #[test]
    fn test_hypothesis_bundle_instance_flags() {
        let hyp = InteractiveHypothesisBundle {
            names: vec!["inst".into()],
            type_: "Add Nat".into(),
            is_instance: true,
            is_inserted: true,
        };
        let json = serde_json::to_string(&hyp).unwrap();
        assert!(json.contains("\"isInstance\":true"));
        assert!(json.contains("\"isInserted\":true"));
    }

    #[test]
    fn test_interactive_goals_empty_roundtrip() {
        let goals = InteractiveGoals { goals: vec![] };
        let json = serde_json::to_string(&goals).unwrap();
        assert_eq!(json, r#"{"goals":[]}"#);
    }

    #[test]
    fn test_diagnostic_serde() {
        let d = InteractiveDiagnostic {
            range: Range {
                start: Position {
                    line: 1,
                    character: 0,
                },
                end: Position {
                    line: 1,
                    character: 10,
                },
            },
            severity: DiagnosticSeverity::Error,
            message: "type mismatch".into(),
        };
        let json = serde_json::to_string(&d).unwrap();
        let parsed: InteractiveDiagnostic = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.severity, DiagnosticSeverity::Error);
        assert_eq!(parsed.range.start.line, 1);
    }

    #[test]
    fn test_diagnostics_params_optional_range() {
        let json = r#"{"textDocument":{"uri":"file:///t.lean"}}"#;
        let p: GetInteractiveDiagnosticsParams = serde_json::from_str(json).unwrap();
        assert!(p.line_range.is_none());

        let json2 = r#"{"textDocument":{"uri":"file:///t.lean"},"lineRange":[5,20]}"#;
        let p2: GetInteractiveDiagnosticsParams = serde_json::from_str(json2).unwrap();
        assert_eq!(p2.line_range, Some((5, 20)));
    }

    // -- Plain-text rendering tests --------------------------------------------

    #[test]
    fn test_render_goal_plain_no_hyps() {
        let goal = make_goal(vec![], "True");
        assert_eq!(render_goal_plain(&goal), "\u{22a2} True");
    }

    #[test]
    fn test_render_goal_plain_with_hyps() {
        let goal = make_goal(vec![("a b", "Nat"), ("h", "a = b")], "b = a");
        assert_eq!(
            render_goal_plain(&goal),
            "a b : Nat\nh : a = b\n\u{22a2} b = a"
        );
    }

    #[test]
    fn test_render_goals_plain_empty_returns_none() {
        let goals = InteractiveGoals { goals: vec![] };
        assert!(render_goals_plain(&goals).is_none());
    }

    #[test]
    fn test_render_goals_plain_multiple() {
        let goals = InteractiveGoals {
            goals: vec![
                make_goal(vec![], "True"),
                make_goal(vec![("h", "False")], "True"),
            ],
        };
        let text = render_goals_plain(&goals).unwrap();
        assert_eq!(text, "\u{22a2} True\n\nh : False\n\u{22a2} True");
    }

    // -- Dispatched endpoint tests (async) ------------------------------------

    #[tokio::test]
    async fn test_handle_get_interactive_goals_returns_empty() {
        let state = crate::handlers::ServerState::default();
        let params = PlainGoalParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///t.lean".into(),
            },
            position: Position::default(),
        };
        let resp = crate::dispatch::dispatch_request(
            "Lean.Widget.getInteractiveGoals",
            Some(serde_json::to_value(params).unwrap()),
            RequestId::Number(1),
            &state,
            None,
        )
        .await;
        assert!(resp.error.is_none());
        let goals: InteractiveGoals = serde_json::from_value(resp.result.unwrap()).unwrap();
        assert!(goals.goals.is_empty());
    }

    #[tokio::test]
    async fn test_handle_get_interactive_diagnostics_returns_empty() {
        let state = crate::handlers::ServerState::default();
        let params = GetInteractiveDiagnosticsParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///t.lean".into(),
            },
            line_range: None,
        };
        let resp = crate::dispatch::dispatch_request(
            "Lean.Widget.getInteractiveDiagnostics",
            Some(serde_json::to_value(params).unwrap()),
            RequestId::Number(2),
            &state,
            None,
        )
        .await;
        assert!(resp.error.is_none());
        let d: InteractiveDiagnostics = serde_json::from_value(resp.result.unwrap()).unwrap();
        assert!(d.diagnostics.is_empty());
    }

    #[tokio::test]
    async fn test_handle_get_plain_goal_returns_null() {
        let state = crate::handlers::ServerState::default();
        let params = PlainGoalParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///t.lean".into(),
            },
            position: Position {
                line: 5,
                character: 0,
            },
        };
        let resp = crate::dispatch::dispatch_request(
            "getPlainGoal",
            Some(serde_json::to_value(params).unwrap()),
            RequestId::Number(3),
            &state,
            None,
        )
        .await;
        assert!(resp.error.is_none());
        assert!(
            resp.result.unwrap().is_null(),
            "empty goals should serialize as null"
        );
    }
}
