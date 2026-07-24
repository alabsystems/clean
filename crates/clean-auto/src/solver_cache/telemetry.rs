// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Telemetry sink for `solver-attempt-record-v1` (Phase 0).
//!
//! The sink is keyed by the `CLEAN_SOLVER_TELEMETRY_DIR` environment variable.
//! When the variable is unset the sink is a no-op with **zero overhead** (no
//! record is built, no digest is computed) — this is the default. When set,
//! each attempt is appended as one JSON line to `attempts.jsonl` in that
//! directory.
//!
//! # Soundness
//!
//! This is instrumentation only. Writing a record never changes solving
//! behaviour, and the records are search-result provenance, not trusted
//! verdicts (see [`super`] module docs).

use crate::smt::SmtStats;
use crate::solver_cache::record::{
    AttemptResult, CacheOutcome, SmtStatsSnapshot, SolverAttemptRecord, SolverEngine,
    SolverIdentity, SCHEMA_ID,
};
use crate::solver_cache::SolverCacheError;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::time::{SystemTime, UNIX_EPOCH};

/// Environment variable naming the telemetry output directory. Unset ⇒ off.
pub(crate) const TELEMETRY_DIR_ENV: &str = "CLEAN_SOLVER_TELEMETRY_DIR";

/// JSONL filename appended to within the telemetry directory.
const ATTEMPTS_FILE: &str = "attempts.jsonl";

/// The fixed Phase-0 strategy id (the `smt → superposition → oracle` order).
pub(crate) const STRATEGY_ID: &str = "smt→superposition→oracle";

/// Whether telemetry capture is enabled (the env var is set and non-empty).
///
/// Cheap fast path: read the env var directly. Callers gate *all* record
/// construction behind this so the disabled path costs one env lookup.
pub(crate) fn is_enabled() -> bool {
    std::env::var_os(TELEMETRY_DIR_ENV).is_some_and(|v| !v.is_empty())
}

/// The configured telemetry directory, if enabled.
fn telemetry_dir() -> Option<PathBuf> {
    std::env::var_os(TELEMETRY_DIR_ENV)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

/// The `clean-auto` solver version: crate version, plus git short sha when this
/// build can resolve one, else the bare crate version.
///
/// Computed once and cached. Git resolution is attempted lazily and only on the
/// telemetry path, so the disabled default never shells out.
pub(crate) fn solver_version() -> &'static str {
    static VERSION: OnceLock<String> = OnceLock::new();
    VERSION.get_or_init(|| {
        let crate_version = env!("CARGO_PKG_VERSION");
        match git_short_sha() {
            Some(sha) => format!("{crate_version}+{sha}"),
            None => crate_version.to_string(),
        }
    })
}

/// Best-effort `git rev-parse --short HEAD`. `None` if git is unavailable or the
/// directory is not a checkout.
fn git_short_sha() -> Option<String> {
    let output = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let sha = String::from_utf8(output.stdout).ok()?.trim().to_string();
    if sha.is_empty() {
        None
    } else {
        Some(sha)
    }
}

/// Snapshot live [`SmtStats`] into the serde-friendly record form.
pub(crate) fn snapshot_smt_stats(stats: &SmtStats) -> SmtStatsSnapshot {
    SmtStatsSnapshot {
        num_vars: stats.num_vars,
        num_clauses: stats.num_clauses,
        num_terms: stats.num_terms,
        sat_conflicts: stats.sat_conflicts,
        sat_decisions: stats.sat_decisions,
        sat_propagations: stats.sat_propagations,
        sat_learned_clauses: stats.sat_learned_clauses,
        theory_check_calls: stats.theory_check_calls,
        theory_conflicts: stats.theory_conflicts,
        theory_propagated_literals: stats.theory_propagated_literals,
        theory_unknowns: stats.theory_unknowns,
        theory_stats: stats
            .theory_stats
            .iter()
            .map(|(name, count)| ((*name).to_string(), *count))
            .collect(),
    }
}

/// Inputs to a single telemetry attempt record, assembled at the dispatch site.
pub(crate) struct AttemptTelemetry {
    /// Obligation key — the goal-type digest.
    pub(crate) obligation_digest: String,
    /// Which engine produced the attempt.
    pub(crate) engine: SolverEngine,
    /// The attempt outcome class.
    pub(crate) result: AttemptResult,
    /// End-to-end wall time for the attempt.
    pub(crate) wall_ms: u64,
    /// `blake3:` digest of the proof term, when one was produced.
    pub(crate) proof_term_digest: Option<String>,
    /// SMT statistics, when the SMT engine ran.
    pub(crate) smt_stats: Option<SmtStatsSnapshot>,
    /// Whether the proof term was served from the cache or freshly solved.
    pub(crate) cache_outcome: CacheOutcome,
}

impl AttemptTelemetry {
    /// Build the pinned record from the assembled telemetry.
    fn into_record(self) -> SolverAttemptRecord {
        let success = self.result == AttemptResult::Proved;
        SolverAttemptRecord {
            schema: SCHEMA_ID.to_string(),
            obligation_digest: self.obligation_digest,
            theory_logic: self.engine.theory_logic().to_string(),
            solver: SolverIdentity {
                name: self.engine.solver_name().to_string(),
                version: solver_version().to_string(),
            },
            strategy: STRATEGY_ID.to_string(),
            result: self.result,
            wall_ms: self.wall_ms,
            success,
            proof_term_digest: self.proof_term_digest,
            smt_stats: self.smt_stats,
            cache_outcome: self.cache_outcome,
            decided_at_epoch_s: now_epoch_s(),
        }
    }
}

/// Emit one attempt record to the telemetry sink.
///
/// No-op when telemetry is disabled. Errors (e.g. an unwritable directory) are
/// logged and swallowed: telemetry must never perturb solving. Returns the
/// record that was written when enabled, for test inspection.
pub(crate) fn emit(telemetry: AttemptTelemetry) -> Option<SolverAttemptRecord> {
    let dir = telemetry_dir()?;
    let record = telemetry.into_record();
    if let Err(error) = append_record(&dir, &record) {
        tracing::warn!(%error, "solver telemetry record append failed (ignored)");
    }
    Some(record)
}

/// Emit a `CacheHit` attempt record for a cache-served proof term.
///
/// Records that a stored proof term was returned for `obligation_digest` without
/// re-running the solver. No-op when telemetry is disabled. Soundness: the served
/// proof term is re-checked by the caller through the kernel exactly as for a
/// freshly-found proof; this record only measures cache effectiveness.
pub(crate) fn emit_cache_hit(
    obligation_digest: &str,
    engine: SolverEngine,
    lookup_ms: u64,
    proof_term_digest: Option<String>,
) -> Option<SolverAttemptRecord> {
    emit(AttemptTelemetry {
        obligation_digest: obligation_digest.to_string(),
        engine,
        result: AttemptResult::Proved,
        wall_ms: lookup_ms,
        proof_term_digest,
        smt_stats: None,
        cache_outcome: CacheOutcome::CacheHit,
    })
}

/// Append one record to `<dir>/attempts.jsonl` under an **explicit** directory.
///
/// The env-independent append used by the Phase-2 ingest endpoint (the service's
/// telemetry dir comes from `$DIR`, not the producer's `CLEAN_SOLVER_TELEMETRY_DIR`).
/// Soundness is unchanged: the appended record is *provenance*, never a verdict.
pub(crate) fn append_to(
    dir: &std::path::Path,
    record: &SolverAttemptRecord,
) -> Result<(), SolverCacheError> {
    append_record(&dir.to_path_buf(), record)
}

/// Append a single record line to `<dir>/attempts.jsonl`, creating the directory
/// and file as needed.
fn append_record(dir: &PathBuf, record: &SolverAttemptRecord) -> Result<(), SolverCacheError> {
    std::fs::create_dir_all(dir).map_err(|e| SolverCacheError::Sink(e.to_string()))?;
    let path = dir.join(ATTEMPTS_FILE);
    let mut line = record.to_jsonl()?;
    line.push('\n');
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(|e| SolverCacheError::Sink(e.to_string()))?;
    file.write_all(line.as_bytes())
        .map_err(|e| SolverCacheError::Sink(e.to_string()))?;
    Ok(())
}

/// Current Unix epoch seconds (0 on the impossible pre-epoch clock).
fn now_epoch_s() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}
