// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Lean 4 infoview interactive-goal payloads.
//!
//! Structured goal data shapes mirroring `Lean.Widget.InteractiveGoal`
//! (<https://lean-lang.org/doc/api/Lean/Widget/InteractiveGoal.html>), plus
//! the plain-text rendering used by `$/lean/plainGoal` and the inverse
//! parser that recovers structure from a plain rendering.
//!
//! This module is the single shared home for these types: both the JSON-RPC
//! server (`clean-server`, TCP/WebSocket protocol) and the LSP server
//! (`clean-lsp`, `$/lean/rpc/call` channel) serve exactly this data shape,
//! so the two channels can never drift apart. Neither transport type
//! (position, range, document identifier) lives here — those stay with the
//! protocol layer that owns them.

use serde::{Deserialize, Serialize};

/// A bundle of hypotheses sharing the same type.
///
/// In the Lean 4 infoview, `a b c : Nat` becomes one bundle with
/// `names: ["a", "b", "c"]` and `type_: "Nat"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InteractiveHypothesisBundle {
    pub names: Vec<String>,
    #[serde(rename = "type")]
    pub type_: String,
    #[serde(default)]
    pub is_instance: bool,
    #[serde(default)]
    pub is_inserted: bool,
}

/// A single tactic goal with hypotheses and target type.
///
/// Mirrors `Lean.Widget.InteractiveGoal`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InteractiveGoal {
    pub hyps: Vec<InteractiveHypothesisBundle>,
    #[serde(rename = "type")]
    pub type_: String,
    /// `"⊢"` for standard goals, `"case <name>"` for named cases.
    #[serde(default = "default_goal_prefix")]
    pub goal_prefix: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub username: Option<String>,
    #[serde(default)]
    pub is_converted: bool,
}

fn default_goal_prefix() -> String {
    "\u{22a2}".to_string()
}

/// Response payload for `Lean.Widget.getInteractiveGoals`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InteractiveGoals {
    pub goals: Vec<InteractiveGoal>,
}

/// Expected type at a term position, with the local context in scope.
///
/// Mirrors `Lean.Widget.InteractiveTermGoal` minus the LSP `range` field,
/// which belongs to the transport layer that knows the document geometry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InteractiveTermGoal {
    pub hyps: Vec<InteractiveHypothesisBundle>,
    #[serde(rename = "type")]
    pub type_: String,
}

// ============================================================================
// Plain-text rendering ($/lean/plainGoal format)
// ============================================================================

/// Render an [`InteractiveGoal`] as plain text matching Lean 4 `$/lean/plainGoal`.
#[must_use]
pub fn render_goal_plain(goal: &InteractiveGoal) -> String {
    let mut lines: Vec<String> = goal
        .hyps
        .iter()
        .map(|h| format!("{} : {}", h.names.join(" "), h.type_))
        .collect();
    lines.push(format!("{} {}", goal.goal_prefix, goal.type_));
    lines.join("\n")
}

/// Render all goals as plain text separated by blank lines.
/// Returns `None` when there are no goals.
#[must_use]
pub fn render_goals_plain(goals: &InteractiveGoals) -> Option<String> {
    if goals.goals.is_empty() {
        return None;
    }
    let rendered: Vec<String> = goals.goals.iter().map(render_goal_plain).collect();
    Some(rendered.join("\n\n"))
}

/// Parse a plain-rendered goal (the `$/lean/plainGoal` format produced by
/// [`render_goal_plain`]) back into a structured [`InteractiveGoal`].
///
/// Recognized line shapes, in order:
/// - a leading `case <name>` line becomes the goal prefix and case username;
/// - `names : type` lines before the turnstile become hypothesis bundles
///   (names split on whitespace, type taken after the first ` : `);
/// - a `⊢ <target>` line starts the goal target; every following line is
///   kept verbatim as a continuation of the (multi-line) target.
///
/// A rendering with no turnstile line yields a hypothesis-free goal whose
/// target is the remaining text, so no input is ever silently dropped.
#[must_use]
pub fn interactive_goal_from_rendered(rendered: &str) -> InteractiveGoal {
    let mut hyps: Vec<InteractiveHypothesisBundle> = Vec::new();
    let mut goal_prefix: Option<String> = None;
    let mut username: Option<String> = None;
    let mut target: Option<String> = None;

    for line in rendered.lines() {
        if let Some(t) = target.as_mut() {
            t.push('\n');
            t.push_str(line);
            continue;
        }
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix('\u{22a2}') {
            target = Some(rest.trim_start().to_string());
        } else if let Some(case_name) = trimmed
            .strip_prefix("case ")
            .filter(|_| goal_prefix.is_none() && hyps.is_empty())
        {
            goal_prefix = Some(trimmed.to_string());
            username = Some(case_name.trim().to_string());
        } else if let Some((names, ty)) = trimmed.split_once(" : ") {
            hyps.push(InteractiveHypothesisBundle {
                names: names.split_whitespace().map(String::from).collect(),
                type_: ty.trim().to_string(),
                is_instance: false,
                is_inserted: false,
            });
        } else if !trimmed.is_empty() {
            // Fail-safe: an unrecognized non-empty line becomes the goal
            // target so no rendering is silently dropped.
            target = Some(trimmed.to_string());
        }
    }

    InteractiveGoal {
        hyps,
        type_: target.unwrap_or_else(|| rendered.trim().to_string()),
        goal_prefix: goal_prefix.unwrap_or_else(default_goal_prefix),
        username,
        is_converted: false,
    }
}

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

    #[test]
    fn test_render_then_parse_roundtrips_hypothesis_bundles() {
        let goal = make_goal(vec![("a b", "Nat"), ("h", "a = b")], "b = a");
        let rendered = render_goal_plain(&goal);
        assert_eq!(rendered, "a b : Nat\nh : a = b\n\u{22a2} b = a");
        let parsed = interactive_goal_from_rendered(&rendered);
        assert_eq!(parsed, goal, "plain rendering should parse back losslessly");
    }

    #[test]
    fn test_parse_bare_turnstile_target_has_no_hyps() {
        let parsed = interactive_goal_from_rendered("\u{22a2} True");
        assert!(parsed.hyps.is_empty());
        assert_eq!(parsed.type_, "True");
        assert_eq!(parsed.goal_prefix, "\u{22a2}");
        assert!(parsed.username.is_none());
    }

    #[test]
    fn test_parse_case_prefixed_rendering_sets_username() {
        let parsed = interactive_goal_from_rendered("case succ\nn : Nat\n\u{22a2} P n");
        assert_eq!(parsed.goal_prefix, "case succ");
        assert_eq!(parsed.username.as_deref(), Some("succ"));
        assert_eq!(parsed.hyps.len(), 1);
        assert_eq!(parsed.hyps[0].names, ["n"]);
        assert_eq!(parsed.hyps[0].type_, "Nat");
        assert_eq!(parsed.type_, "P n");
    }

    #[test]
    fn test_parse_no_turnstile_keeps_whole_text_as_target() {
        let parsed = interactive_goal_from_rendered("True");
        assert!(parsed.hyps.is_empty());
        assert_eq!(parsed.type_, "True");
    }

    #[test]
    fn test_parse_multiline_target_keeps_continuation_lines() {
        let parsed = interactive_goal_from_rendered("\u{22a2} \u{2200} x,\n  P x");
        assert_eq!(parsed.type_, "\u{2200} x,\n  P x");
    }

    #[test]
    fn test_parse_hypothesis_type_containing_colon_splits_at_first() {
        let parsed = interactive_goal_from_rendered("h : a : b\n\u{22a2} G");
        assert_eq!(parsed.hyps.len(), 1);
        assert_eq!(parsed.hyps[0].names, ["h"]);
        assert_eq!(parsed.hyps[0].type_, "a : b");
    }

    #[test]
    fn test_interactive_goal_serde_camel_case_shape() {
        let goal = make_goal(vec![("h", "P")], "Q");
        let json = serde_json::to_string(&goal).unwrap();
        assert!(json.contains("\"goalPrefix\""));
        assert!(json.contains("\"type\":\"Q\""));
        assert!(json.contains("\"isConverted\":false"));
        assert!(
            !json.contains("username"),
            "None username should be skipped"
        );
        let parsed: InteractiveGoal = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, goal);
    }

    #[test]
    fn test_interactive_goal_default_prefix_on_deserialize() {
        let json = r#"{"hyps":[],"type":"True"}"#;
        let goal: InteractiveGoal = serde_json::from_str(json).unwrap();
        assert_eq!(goal.goal_prefix, "\u{22a2}");
        assert!(!goal.is_converted);
    }

    #[test]
    fn test_interactive_term_goal_serde_shape() {
        let term_goal = InteractiveTermGoal {
            hyps: vec![InteractiveHypothesisBundle {
                names: vec!["inst".into()],
                type_: "Add Nat".into(),
                is_instance: true,
                is_inserted: false,
            }],
            type_: "Nat".into(),
        };
        let json = serde_json::to_string(&term_goal).unwrap();
        assert!(json.contains("\"type\":\"Nat\""));
        assert!(json.contains("\"isInstance\":true"));
        let parsed: InteractiveTermGoal = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, term_goal);
    }

    #[test]
    fn test_render_goals_plain_empty_returns_none() {
        let goals = InteractiveGoals { goals: vec![] };
        assert!(render_goals_plain(&goals).is_none());
    }

    #[test]
    fn test_render_goals_plain_multiple_separated_by_blank_line() {
        let goals = InteractiveGoals {
            goals: vec![
                make_goal(vec![], "True"),
                make_goal(vec![("h", "False")], "True"),
            ],
        };
        let text = render_goals_plain(&goals).unwrap();
        assert_eq!(text, "\u{22a2} True\n\nh : False\n\u{22a2} True");
    }
}
