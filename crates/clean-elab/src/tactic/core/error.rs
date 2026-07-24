// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic error types.

use crate::agent_diagnostics::AgentDiagnostic;
use crate::ElabError;
use clean_auto::bridge::BridgeError;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Result type for tactic execution
pub type TacticResult = Result<(), TacticError>;

/// Candidate subterm reported when a rewrite rule fails to match.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RewriteCandidate {
    /// Stable structural path from the focused expression root.
    pub path: String,
    /// Rendered subterm at `path`.
    pub subterm: String,
}

impl RewriteCandidate {
    /// Create a rewrite candidate.
    #[must_use]
    pub fn new(path: impl Into<String>, subterm: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            subterm: subterm.into(),
        }
    }
}

/// Errors that can occur during tactic execution
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum TacticError {
    #[error("no goals")]
    NoGoals,

    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("goal mismatch: {0}")]
    GoalMismatch(String),

    #[error("unknown identifier: {0}")]
    UnknownIdent(String),

    #[error("unknown tactic '{0}'")]
    UnknownTactic(String),

    #[error("type check failed: {0}")]
    TypeCheckFailed(String),

    #[error("unification failed: {0}")]
    UnificationFailed(String),

    #[error("hypothesis not found: {0}")]
    HypothesisNotFound(String),

    #[error("{tactic}: requires {expected}")]
    MissingArgument { tactic: String, expected: String },

    #[error("{tactic}: no progress made")]
    NoProgress { tactic: String },

    #[error(
        "{tactic}: rewrite rule {rule} did not match focused subterm; searched for {searched_for} in {focus}"
    )]
    RewriteNoMatch {
        tactic: String,
        rule: String,
        direction: String,
        searched_for: String,
        focus: String,
        focus_path: Vec<String>,
        candidates: Vec<RewriteCandidate>,
    },

    #[error(
        "{tactic}: failed to lift rewrite proof for {rule} through focused subterm at {}",
        focus_path.join(".")
    )]
    RewriteProofLiftFailed {
        tactic: String,
        rule: String,
        direction: String,
        searched_for: String,
        replacement: String,
        focus_before: String,
        focus_after: String,
        focus_path: Vec<String>,
    },

    #[error("{constant} not found in environment")]
    EnvironmentMissing { constant: String },

    #[error("could not synthesize {class} instance for {ty}")]
    InstanceSynthesisFailed { class: String, ty: String },

    #[error("{tactic}: {reason}")]
    ArithmeticFailed { tactic: String, reason: String },

    #[error("unfold failed: {name}: {reason}")]
    UnfoldFailed { name: String, reason: String },

    #[error("{detail}")]
    Timeout { detail: String },

    #[error("{combinator}: all tactics failed")]
    AllTacticsFailed { combinator: String },

    #[error("unsolved goals: tactic block has {count} unsolved goal(s){detail}")]
    UnsolvedGoals { count: usize, detail: String },

    #[error("{tactic}: exceeded max depth {max_depth}")]
    DepthExceeded { tactic: String, max_depth: usize },

    #[error("{tactic}: {detail}")]
    SearchExhausted { tactic: String, detail: String },

    #[error("{tactic}: SMT {detail}")]
    SmtFailed { tactic: String, detail: String },

    #[error("{tactic}: bridge {source}")]
    BridgeFailed {
        tactic: String,
        #[source]
        source: BridgeError,
    },

    #[error("oracle: {detail}")]
    OracleFailed { detail: String },

    #[error("{rule}: {detail}")]
    RuleApplicationFailed { rule: String, detail: String },

    #[error("{tactic}: {detail}")]
    InvalidTarget { tactic: String, detail: String },

    #[error("elaboration failed: {detail}")]
    ElaborationFailed { detail: String },

    /// A user metaprogram raised a custom error via `throwError "msg"` (or an
    /// alias). The `message` is the literal string the user passed. This is a
    /// plain typed diagnostic: it closes no goal, accepts no term, and fabricates
    /// nothing — it only makes elaboration FAIL with exactly the user's message.
    #[error("{message}")]
    UserThrowError { message: String },

    #[error("elaboration failed: {source}")]
    UpstreamElabError {
        #[source]
        source: Box<ElabError>,
    },

    #[error("tactic block completed but no proof term produced")]
    ProofNotProduced,

    #[error("{tactic}: parse error: {detail}")]
    ParseFailed { tactic: String, detail: String },
}

impl TacticError {
    #[must_use]
    pub(crate) fn is_recoverable_first_failure(&self) -> bool {
        matches!(
            self,
            Self::GoalMismatch(_)
                | Self::HypothesisNotFound(_)
                | Self::UnificationFailed(_)
                | Self::UnfoldFailed { .. }
                | Self::Timeout { .. }
                | Self::AllTacticsFailed { .. }
                | Self::UnsolvedGoals { .. }
                | Self::DepthExceeded { .. }
                | Self::SearchExhausted { .. }
                | Self::SmtFailed { .. }
                | Self::BridgeFailed { .. }
                | Self::RuleApplicationFailed { .. }
                | Self::InvalidTarget { .. }
                | Self::ArithmeticFailed { .. }
                | Self::NoProgress { .. }
                | Self::RewriteNoMatch { .. }
                | Self::RewriteProofLiftFailed { .. }
                | Self::OracleFailed { .. }
                // A branch whose ATTEMPT to close the goal failed — `rfl`/`exact`
                // on a non-matching goal (`TypeMismatch`/`TypeCheckFailed`), a
                // term whose instance/constant couldn't be resolved, or a term
                // that simply wasn't produced. Lean 4's `first` backtracks on any
                // such tactic failure and tries the next branch; these were
                // missing, so `first | rfl | exact h` propagated `rfl`'s
                // `TypeMismatch` instead of falling through to `exact h`.
                | Self::TypeMismatch { .. }
                | Self::TypeCheckFailed(_)
                | Self::InstanceSynthesisFailed { .. }
                | Self::UnknownIdent(_)
                | Self::EnvironmentMissing { .. }
                | Self::ProofNotProduced
                | Self::ElaborationFailed { .. }
                | Self::UpstreamElabError { .. }
        )
    }

    pub(crate) fn from_elab_error(err: ElabError) -> Self {
        match err {
            ElabError::TacticFailed(err) => err,
            other => Self::UpstreamElabError {
                source: Box::new(other),
            },
        }
    }

    #[must_use]
    pub fn agent_diagnostics(&self) -> Vec<AgentDiagnostic> {
        match self {
            Self::RewriteNoMatch {
                tactic,
                rule,
                direction,
                searched_for,
                focus,
                focus_path,
                candidates,
            } => {
                let mut diag = AgentDiagnostic::error(
                    "rewrite.no_match",
                    format!("{tactic}: rewrite rule `{rule}` did not match the focused subterm"),
                )
                .with_facts([
                    ("tactic", tactic.clone()),
                    ("rule", rule.clone()),
                    ("direction", direction.clone()),
                    ("rewritePattern", searched_for.clone()),
                    ("searchedFor", searched_for.clone()),
                    ("failedSubterm", focus.clone()),
                    ("failedSubtermPath", format_focus_path(focus_path)),
                    ("focus", focus.clone()),
                    ("focusPath", format_focus_path(focus_path)),
                    ("candidateCount", candidates.len().to_string()),
                ]);
                for (idx, candidate) in candidates.iter().enumerate() {
                    diag = diag
                        .with_fact(format!("candidate.{idx}.path"), candidate.path.clone())
                        .with_fact(
                            format!("candidate.{idx}.subterm"),
                            candidate.subterm.clone(),
                        )
                        .with_related(
                            format!(
                                "nearby subterm at `{}`: `{}`",
                                candidate.path, candidate.subterm
                            ),
                            None,
                        );
                    diag = diag.with_suggestion(
                        format!("nearby subterm at `{}`", candidate.path),
                        Some(candidate.subterm.clone()),
                    );
                }
                vec![diag]
            }
            Self::RewriteProofLiftFailed {
                tactic,
                rule,
                direction,
                searched_for,
                replacement,
                focus_before,
                focus_after,
                focus_path,
            } => vec![AgentDiagnostic::error(
                "rewrite.proof_lift_failed",
                format!("{tactic}: rewrite matched but proof lifting failed"),
            )
            .with_facts([
                ("tactic", tactic.clone()),
                ("rule", rule.clone()),
                ("direction", direction.clone()),
                ("rewritePattern", searched_for.clone()),
                ("searchedFor", searched_for.clone()),
                ("replacement", replacement.clone()),
                ("failedSubterm", focus_before.clone()),
                ("failedSubtermPath", format_focus_path(focus_path)),
                ("focusBefore", focus_before.clone()),
                ("focusAfter", focus_after.clone()),
                ("focusPath", format_focus_path(focus_path)),
            ])],
            Self::UpstreamElabError { source } => source.agent_diagnostics(),
            _ => Vec::new(),
        }
    }
}

fn format_focus_path(path: &[String]) -> String {
    if path.is_empty() {
        "root".to_owned()
    } else {
        path.join(".")
    }
}
