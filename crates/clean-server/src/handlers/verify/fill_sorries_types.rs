// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type definitions for `fillSorries` and related file-level theorem extraction.

use crate::proof_state::{MathverseCandidate, RelevantLemma, StateId};
use serde::{Deserialize, Serialize};

/// Fill `sorry` holes in a Lean file using an automatic tactic sequence.
#[derive(Debug, Clone, Deserialize)]
pub struct FillSorriesParams {
    /// Complete Lean file content
    pub content: String,
    /// Optional tactic sequence to try for each `sorry`.
    ///
    /// When omitted or empty, the server uses the default SorryHammer-style
    /// sequence: `omega`, `linarith`, `simp`, `ring`, `norm_num`, `ay_smt`,
    /// `aesop`.
    #[serde(default)]
    pub tactic_sequence: Vec<String>,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Result of automatic `sorry` filling.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FillSorriesResult {
    /// Whether the rewritten proof closes all goals and kernel-checks.
    pub verified: bool,
    /// Extracted theorem information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub theorem: Option<ExtractedTheorem>,
    /// Rewritten tactic script with one tactic per line.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub filled_proof: Option<String>,
    /// `sorry` positions in the normalized original proof script.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub original_sorries: Vec<SorryLocation>,
    /// Remaining `sorry` positions in `filled_proof`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub remaining_sorries: Vec<SorryLocation>,
    /// Number of original `sorry` holes replaced by automatic tactics.
    pub solved_sorries: usize,
    /// Total time in nanoseconds
    pub time_ns: u64,
    /// Timing breakdown
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timing: Option<super::TimingBreakdown>,
    /// Error if filling failed before the proof could be replayed completely
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<super::VerifyProofError>,
    /// Axiom usage summary for the rewritten proof
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<super::TrustSummary>,
    /// Kernel proof term (Lean syntax) when the proof is fully verified.
    ///
    /// Present only when `verified` is true and the proof state has a closed
    /// proof. This enables the promotion pipeline to accept proof terms
    /// extracted from tactic-based proofs.
    ///
    /// Part of #3221: searchProof decompose_then_search proof term extraction.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_term: Option<String>,
    /// Structured goal states at each sorry hole (Pantograph-style extraction).
    ///
    /// Contains the proof context (hypotheses, target) at each sorry location,
    /// enabling LLM agents to generate focused tactics per-goal instead of
    /// operating on the whole file.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sorry_goals: Vec<SorryGoalInfo>,
}

/// Hypothesis available in a sorry hole's local context.
///
/// Lightweight format for LLM consumption: pretty-printed strings only, no
/// full kernel `Expr` serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SorryHypothesis {
    /// Hypothesis name (e.g., "h", "n", "ih")
    pub name: String,
    /// Pretty-printed type (e.g., "n < m", "Nat")
    pub type_pp: String,
    /// Pretty-printed value for let-bindings
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value_pp: Option<String>,
}

/// A single goal at a sorry site.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SorryGoal {
    /// Goal identifier within this sorry snapshot.
    pub goal_id: String,
    /// Pretty-printed target type to prove (e.g., "n + 1 > 0")
    pub target: String,
    /// Optional goal tag propagated by branching tactics (`cases`, `induction`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tag: Option<String>,
    /// Hypotheses available in the local context
    pub hypotheses: Vec<SorryHypothesis>,
}

/// Structured goal-state information for a single sorry hole.
///
/// Enables Pantograph-style feedback loops: the caller (LLM agent) receives
/// the precise proof context at each sorry, enabling targeted tactic
/// generation without needing the whole file.
///
/// For unsolved sorries, `state_id` links into the proof state cache so the
/// caller can resume interactive tactic application via `applyTactic`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SorryGoalInfo {
    /// 0-indexed sorry number in the original proof script.
    pub sorry_index: usize,
    /// Whether this sorry was solved by the automatic tactic sequence.
    pub solved: bool,
    /// The tactic that solved this sorry (if solved).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replacement_tactic: Option<String>,
    /// Cached proof state ID at this sorry site.
    ///
    /// Present for unsolved sorries when state caching is available. Callers
    /// can pass this to `applyTactic` to try their own tactics interactively,
    /// enabling the iterative Pantograph-style feedback loop.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub state_id: Option<StateId>,
    /// Search hints for the currently focused goal at this sorry.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub search_hints: Vec<String>,
    /// Suggested tactics for the focused goal in machine-friendly form.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggested_tactics: Vec<String>,
    /// Relevant lemmas selected for the focused goal.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub relevant_lemmas: Vec<RelevantLemma>,
    /// Trust-filtered Mathverse Library candidates for the focused goal.
    #[serde(default)]
    pub mathverse_candidates: Vec<MathverseCandidate>,
    /// Goals active at the sorry site before fill was attempted.
    /// Typically one main goal, but can be multiple after `constructor`
    /// or `cases`.
    pub goals: Vec<SorryGoal>,
}

/// Extracted theorem from file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtractedTheorem {
    /// Theorem name (e.g., "fate_x_001")
    pub name: String,
    /// Full type/goal signature
    pub goal: String,
    /// Line number where theorem starts
    pub line: usize,
    /// Original proof (before replacement)
    pub original_proof: String,
}

/// Location of a sorry in the file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SorryLocation {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub col: usize,
    /// Context (enclosing theorem name if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<String>,
}
