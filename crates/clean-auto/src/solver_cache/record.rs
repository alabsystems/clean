// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `solver-attempt-record-v1`: one row per solving attempt.
//!
//! Phase-0 subset of the schema pinned in
//! `designs/2026-06-24-solver-results-cache-service.md` §3. This is pure
//! telemetry — the record is *provenance*, never a trusted verdict. A
//! `proof_term_digest` is recorded so a future cache hit can return the proof
//! term, but the caller (swarm / graduation) re-checks that term through the
//! kernel exactly as for a freshly-found proof. A raw solver verdict without a
//! proof term (`Unsat`/`Unknown`/`Timeout`) is a hint, never a verification.

use serde::{Deserialize, Serialize};

/// Schema identifier for the pinned record format.
pub(crate) const SCHEMA_ID: &str = "solver-attempt-record-v1";

/// Whether the cache served this attempt or the solver did (design §3 telemetry).
///
/// Soundness note: `Hit` records that the proof term came *from the cache*, not
/// that it was trusted — the caller re-checks the served term through the kernel
/// exactly as for a freshly-found proof. This field has zero soundness weight; it
/// measures the cache's effectiveness only.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum CacheOutcome {
    /// The solver ran; no cached proof term was available (or the cache was off).
    #[default]
    Miss,
    /// A cached proof term was served, short-circuiting the solver search.
    CacheHit,
}

/// Outcome of a single solving attempt.
///
/// `Proved` is the only proof-bearing result; all others are advisory
/// telemetry. `Proved` records carry a `proof_term_digest` so a cache layer can
/// return the proof term, which the caller still re-checks through the kernel.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum AttemptResult {
    /// A kernel-checkable proof term was produced.
    Proved,
    /// The solver reported the goal satisfiable / found a counter-model.
    Sat,
    /// The solver reported unsatisfiable but produced no replayable proof term.
    Unsat,
    /// The solver could not decide the goal.
    Unknown,
    /// The attempt hit its resource budget.
    Timeout,
    /// A proof search ran but produced no proof term (e.g. reconstruction failed).
    Noproof,
}

/// Which automation engine produced the attempt.
///
/// Mirrors [`crate::AutomationSource`] but is `serde`-serializable and lives in
/// the telemetry layer so the engine enum stays a pure dispatch type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum SolverEngine {
    /// SMT bridge / DPLL(T).
    CleanSmt,
    /// Saturation-based superposition prover.
    CleanSuperposition,
    /// Neural / LLM proof oracle.
    Oracle,
}

impl SolverEngine {
    /// The `solver_name` field value for this engine.
    pub(crate) fn solver_name(self) -> &'static str {
        match self {
            Self::CleanSmt => "clean-smt",
            Self::CleanSuperposition => "clean-superposition",
            Self::Oracle => "oracle",
        }
    }

    /// The default `theory_logic` tag for this engine.
    ///
    /// Phase 0 records the native logic; the SMT-LIB sub-logic refinement
    /// (`QF_UFLIA` etc.) is a later phase.
    pub(crate) fn theory_logic(self) -> &'static str {
        match self {
            Self::CleanSmt | Self::CleanSuperposition => "clean-cic",
            Self::Oracle => "oracle",
        }
    }
}

/// `solver{name,version}` sub-object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverIdentity {
    /// Engine name (`clean-smt`, `clean-superposition`, `oracle`).
    pub(crate) name: String,
    /// `clean-auto` crate version plus git short sha when available, else the
    /// bare crate version.
    pub(crate) version: String,
}

/// Serde-friendly snapshot of [`crate::smt::SmtStats`].
///
/// `SmtStats`' fields are `pub(crate)` and the type does not derive `Serialize`,
/// so the record captures a flat copy rather than depending on the solver type's
/// serialization.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SmtStatsSnapshot {
    pub(crate) num_vars: usize,
    pub(crate) num_clauses: usize,
    pub(crate) num_terms: usize,
    pub(crate) sat_conflicts: u64,
    pub(crate) sat_decisions: u64,
    pub(crate) sat_propagations: u64,
    pub(crate) sat_learned_clauses: u64,
    pub(crate) theory_check_calls: u64,
    pub(crate) theory_conflicts: u64,
    pub(crate) theory_propagated_literals: u64,
    pub(crate) theory_unknowns: u64,
    /// Per-theory `(name, count)` pairs.
    pub(crate) theory_stats: Vec<(String, u64)>,
}

/// One row per solving attempt — `solver-attempt-record-v1` (Phase-0 subset).
///
/// Forward-compatible: unknown fields deserialize via `#[serde(default)]` on the
/// optional fields, mirroring the graduation-record conventions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverAttemptRecord {
    /// Schema discriminator. Always [`SCHEMA_ID`] at insert.
    pub(crate) schema: String,

    // ── IDENTITY ────────────────────────────────────────────────────
    /// `blake3:<64hex>` content address of the goal type (the obligation key).
    pub(crate) obligation_digest: String,

    // ── SOLVER CONTRACT ─────────────────────────────────────────────
    /// SMT-LIB logic or `clean-cic` for native engines.
    pub(crate) theory_logic: String,
    /// Engine identity + version.
    pub(crate) solver: SolverIdentity,
    /// Within-engine strategy id (the fixed `smt→superposition→oracle` order).
    pub(crate) strategy: String,

    // ── RESULT ──────────────────────────────────────────────────────
    /// The cached outcome class.
    pub(crate) result: AttemptResult,
    /// End-to-end wall time for this attempt, in milliseconds.
    pub(crate) wall_ms: u64,
    /// `true` iff a kernel-checkable proof term was produced (`result == Proved`).
    pub(crate) success: bool,
    /// `blake3:` digest of the produced proof term, when `result == Proved`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_term_digest: Option<String>,

    // ── TELEMETRY (effectiveness, NOT soundness) ────────────────────
    /// SMT statistics, when the SMT engine ran.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) smt_stats: Option<SmtStatsSnapshot>,
    /// Whether this attempt was served from the cache or freshly solved.
    ///
    /// Defaulted for forward compatibility with Phase-0 telemetry-only logs that
    /// predate the cache-hit hook. Zero soundness weight (a `CacheHit` proof term
    /// is still kernel-re-checked by the caller).
    #[serde(default)]
    pub(crate) cache_outcome: CacheOutcome,
    /// Unix epoch seconds at which the attempt was recorded.
    pub(crate) decided_at_epoch_s: u64,
}

impl SolverAttemptRecord {
    /// Serialize to a single JSONL line (no trailing newline).
    pub(crate) fn to_jsonl(&self) -> Result<String, super::SolverCacheError> {
        serde_json::to_string(self).map_err(|e| super::SolverCacheError::Serialize(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_record() -> SolverAttemptRecord {
        SolverAttemptRecord {
            schema: SCHEMA_ID.to_string(),
            obligation_digest: "blake3:".to_string() + &"ab".repeat(32),
            theory_logic: SolverEngine::CleanSmt.theory_logic().to_string(),
            solver: SolverIdentity {
                name: SolverEngine::CleanSmt.solver_name().to_string(),
                version: "1.2.0".to_string(),
            },
            strategy: "smt→superposition→oracle".to_string(),
            result: AttemptResult::Proved,
            wall_ms: 42,
            success: true,
            proof_term_digest: Some("blake3:".to_string() + &"cd".repeat(32)),
            smt_stats: Some(SmtStatsSnapshot::default()),
            cache_outcome: CacheOutcome::Miss,
            decided_at_epoch_s: 1_750_000_000,
        }
    }

    #[test]
    fn test_record_jsonl_roundtrip() {
        let record = sample_record();
        let line = record.to_jsonl().expect("serialize");
        assert!(!line.contains('\n'), "JSONL line must be single-line");
        let parsed: SolverAttemptRecord =
            serde_json::from_str(&line).expect("deserialize round-trip");
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_record_schema_field_pinned() {
        let line = sample_record().to_jsonl().expect("serialize");
        assert!(
            line.contains("\"schema\":\"solver-attempt-record-v1\""),
            "schema id must be pinned in the record: {line}"
        );
    }

    #[test]
    fn test_result_serializes_lowercase() {
        assert_eq!(
            serde_json::to_string(&AttemptResult::Noproof).expect("ser"),
            "\"noproof\""
        );
        assert_eq!(
            serde_json::to_string(&AttemptResult::Timeout).expect("ser"),
            "\"timeout\""
        );
    }

    #[test]
    fn test_success_implies_proof_term_present_for_proved() {
        let record = sample_record();
        assert!(record.success);
        assert!(record.proof_term_digest.is_some());
    }
}
