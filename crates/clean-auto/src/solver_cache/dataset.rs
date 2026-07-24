// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NN training-data export over the solver telemetry stream (Phase 1, §6).
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §6. The same
//! `solver-attempt-record-v1` rows that drive [`super::analysis`] *are* the
//! dataset for a learned strategy selector. This module emits one JSONL row per
//! attempt as `(feature_vector, strategy_id, label_block, provenance)`.
//!
//! Phase 1 exports JSONL (Parquet is a Phase-2 concern — it needs a columnar
//! writer dependency the design defers). The exporter bakes in the design's
//! caveats:
//!
//! - **Labels are solver-specific and non-transferable** — each row's labels
//!   describe *Clean's own* engine on that instance, never a third-party solver.
//! - **Reconstruct full attempt sets** — VBS/SBS need every engine's attempt for
//!   an instance, so the exporter preserves the `obligation_digest` on every row
//!   and never drops "loss" rows; the consumer groups siblings by it.
//! - **Oracle cost is not CPU** — the `oracle` engine's `wall_ms` is
//!   network-latency, flagged per-row via `engine_cost_is_cpu` so a downstream
//!   trainer can normalise.
//!
//! # Soundness
//!
//! Pure data export; no soundness weight. A row is a *record of what happened*,
//! never a claim about provability.

use std::io::Write;
use std::path::Path;

use serde::Serialize;
use thiserror::Error;

use super::analysis::DEFAULT_TIMEOUT_BUDGET_MS;
use super::record::{AttemptResult, CacheOutcome, SolverAttemptRecord};

/// Errors writing a dataset file.
#[derive(Debug, Error)]
pub(crate) enum DatasetError {
    /// An I/O error writing the output file.
    #[error("write dataset {path}: {source}")]
    Io {
        /// Output path.
        path: String,
        /// Underlying I/O error.
        source: std::io::Error,
    },
    /// Serializing a dataset row to JSON failed.
    #[error("serialize dataset row: {0}")]
    Serialize(String),
}

/// Cheap, static features available from a Phase-0 attempt record (design §6.1).
///
/// Phase 0 records do not yet carry the full `GoalFeatures` (size/depth/head
/// symbol); what *is* available is the obligation identity + the SMT probe stats
/// when the SMT engine ran. Those probe stats are SATzilla's strongest signal,
/// so they are the Phase-1 feature core; the richer static features are a later
/// schema extension flagged in the design.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct FeatureVector {
    /// SAT conflicts from the SMT probe (`None` if the SMT engine did not run).
    pub(crate) sat_conflicts: Option<u64>,
    /// SAT decisions from the SMT probe.
    pub(crate) sat_decisions: Option<u64>,
    /// SAT propagations from the SMT probe.
    pub(crate) sat_propagations: Option<u64>,
    /// Learned clauses from the SMT probe.
    pub(crate) sat_learned_clauses: Option<u64>,
    /// Theory-check calls from the SMT probe.
    pub(crate) theory_check_calls: Option<u64>,
    /// Theory `unknown` density from the SMT probe.
    pub(crate) theory_unknowns: Option<u64>,
    /// Number of CNF variables in the SMT encoding.
    pub(crate) num_vars: Option<usize>,
    /// Number of CNF clauses in the SMT encoding.
    pub(crate) num_clauses: Option<usize>,
    /// Number of SMT terms.
    pub(crate) num_terms: Option<usize>,
}

impl FeatureVector {
    fn from_record(r: &SolverAttemptRecord) -> Self {
        match &r.smt_stats {
            Some(s) => Self {
                sat_conflicts: Some(s.sat_conflicts),
                sat_decisions: Some(s.sat_decisions),
                sat_propagations: Some(s.sat_propagations),
                sat_learned_clauses: Some(s.sat_learned_clauses),
                theory_check_calls: Some(s.theory_check_calls),
                theory_unknowns: Some(s.theory_unknowns),
                num_vars: Some(s.num_vars),
                num_clauses: Some(s.num_clauses),
                num_terms: Some(s.num_terms),
            },
            None => Self::default(),
        }
    }
}

/// The label block (Y) for one attempt (design §6.2).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct LabelBlock {
    /// The attempt outcome (`proved`/`timeout`/...).
    pub(crate) result: String,
    /// End-to-end wall time (ms).
    pub(crate) wall_ms: u64,
    /// The PAR-2 timeout budget the `par2_score` assumes.
    pub(crate) timeout_budget_ms: u64,
    /// The fused PAR-2 label: `wall_ms` if solved, else `2 × budget`.
    pub(crate) par2_score: u64,
    /// `blake3:` digest of the produced proof term (the *success cache* — return
    /// the cached proof, not just "solvable"). `None` for non-`Proved` rows.
    pub(crate) certificate_ref: Option<String>,
}

/// Provenance attached to every dataset row.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DatasetProvenance {
    /// The obligation identity — siblings (multiple engines on one instance)
    /// share this so the consumer can reconstruct full attempt sets for VBS/SBS.
    pub(crate) obligation_digest: String,
    /// Engine that produced the row.
    pub(crate) solver: String,
    /// Engine version.
    pub(crate) solver_version: String,
    /// Theory logic.
    pub(crate) theory_logic: String,
    /// Whether this row came from a cache hit (effectiveness, not soundness).
    pub(crate) cache_hit: bool,
    /// Unix epoch seconds of the attempt.
    pub(crate) decided_at_epoch_s: u64,
}

/// One exported dataset row: `(features, strategy, labels, provenance)`.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DatasetRow {
    /// Static + probe features (X).
    pub(crate) features: FeatureVector,
    /// The strategy id that produced this attempt.
    pub(crate) strategy_id: String,
    /// `false` for the `oracle` engine (its `wall_ms` is network latency + token
    /// cost, NOT CPU time): a trainer must normalise oracle cost per design §6.3.
    pub(crate) engine_cost_is_cpu: bool,
    /// The label block (Y).
    pub(crate) labels: LabelBlock,
    /// Row provenance.
    pub(crate) provenance: DatasetProvenance,
}

impl DatasetRow {
    /// Project one attempt record into a dataset row.
    pub(crate) fn from_record(r: &SolverAttemptRecord, budget_ms: u64) -> Self {
        let par2_score = if r.result == AttemptResult::Proved {
            r.wall_ms
        } else {
            budget_ms.saturating_mul(2)
        };
        // The `oracle` engine's runtime is network latency, not CPU; flag it so a
        // trainer normalises (design §6.3).
        let engine_cost_is_cpu = r.solver.name != "oracle";
        DatasetRow {
            features: FeatureVector::from_record(r),
            strategy_id: r.strategy.clone(),
            engine_cost_is_cpu,
            labels: LabelBlock {
                result: serde_json::to_value(r.result)
                    .ok()
                    .and_then(|v| v.as_str().map(str::to_string))
                    .unwrap_or_default(),
                wall_ms: r.wall_ms,
                timeout_budget_ms: budget_ms,
                par2_score,
                certificate_ref: r.proof_term_digest.clone(),
            },
            provenance: DatasetProvenance {
                obligation_digest: r.obligation_digest.clone(),
                solver: r.solver.name.clone(),
                solver_version: r.solver.version.clone(),
                theory_logic: r.theory_logic.clone(),
                cache_hit: r.cache_outcome == CacheOutcome::CacheHit,
                decided_at_epoch_s: r.decided_at_epoch_s,
            },
        }
    }
}

/// Filters applied while exporting (design §6.3 `--engine` / `--theory`).
#[derive(Clone, Debug, Default)]
pub struct ExportFilter {
    /// Restrict to one engine name (`clean-smt` / `clean-superposition` / `oracle`).
    pub engine: Option<String>,
    /// Restrict to one `theory_logic`.
    pub theory: Option<String>,
}

impl ExportFilter {
    fn admits(&self, r: &SolverAttemptRecord) -> bool {
        self.engine.as_deref().is_none_or(|e| r.solver.name == e)
            && self.theory.as_deref().is_none_or(|t| r.theory_logic == t)
    }
}

/// Project the admitted attempt rows into in-memory [`DatasetRow`]s.
///
/// Shared by [`export_jsonl`] (the file exporter) and the Phase-2 service's
/// `/export-dataset` endpoint (which serializes the rows into the HTTP response
/// instead of a file). Same filter + caveats; no soundness weight.
pub(crate) fn rows(
    records: &[SolverAttemptRecord],
    filter: &ExportFilter,
    budget_ms: u64,
) -> Vec<DatasetRow> {
    records
        .iter()
        .filter(|r| filter.admits(r))
        .map(|r| DatasetRow::from_record(r, budget_ms))
        .collect()
}

/// Export attempt rows to `out` as JSONL (one [`DatasetRow`] per line).
///
/// `budget_ms` is the PAR-2 budget for the `par2_score` label (use
/// [`DEFAULT_TIMEOUT_BUDGET_MS`] when no per-record budget is available).
/// Returns the number of rows written.
pub(crate) fn export_jsonl(
    rows: &[SolverAttemptRecord],
    filter: &ExportFilter,
    budget_ms: u64,
    out: &Path,
) -> Result<u64, DatasetError> {
    let file = std::fs::File::create(out).map_err(|e| DatasetError::Io {
        path: out.display().to_string(),
        source: e,
    })?;
    let mut writer = std::io::BufWriter::new(file);
    let mut written = 0u64;
    for r in rows.iter().filter(|r| filter.admits(r)) {
        let row = DatasetRow::from_record(r, budget_ms);
        let line =
            serde_json::to_string(&row).map_err(|e| DatasetError::Serialize(e.to_string()))?;
        writeln!(writer, "{line}").map_err(|e| DatasetError::Io {
            path: out.display().to_string(),
            source: e,
        })?;
        written += 1;
    }
    writer.flush().map_err(|e| DatasetError::Io {
        path: out.display().to_string(),
        source: e,
    })?;
    Ok(written)
}

/// The PAR-2 budget the exporter falls back to when none is supplied.
pub(crate) fn default_budget_ms() -> u64 {
    DEFAULT_TIMEOUT_BUDGET_MS
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_cache::record::{SmtStatsSnapshot, SolverIdentity, SCHEMA_ID};

    fn row(solver: &str, result: AttemptResult, wall_ms: u64, smt: bool) -> SolverAttemptRecord {
        SolverAttemptRecord {
            schema: SCHEMA_ID.to_string(),
            obligation_digest: "blake3:".to_string() + &"ab".repeat(32),
            theory_logic: "clean-cic".to_string(),
            solver: SolverIdentity {
                name: solver.to_string(),
                version: "1.2.0".to_string(),
            },
            strategy: "smt→superposition→oracle".to_string(),
            result,
            wall_ms,
            success: result == AttemptResult::Proved,
            proof_term_digest: (result == AttemptResult::Proved)
                .then(|| "blake3:".to_string() + &"cd".repeat(32)),
            smt_stats: smt.then(|| SmtStatsSnapshot {
                sat_conflicts: 7,
                num_vars: 3,
                ..Default::default()
            }),
            cache_outcome: CacheOutcome::Miss,
            decided_at_epoch_s: 1_750_000_000,
        }
    }

    #[test]
    fn test_row_par2_and_certificate() {
        let proved =
            DatasetRow::from_record(&row("clean-smt", AttemptResult::Proved, 30, true), 5000);
        assert_eq!(proved.labels.par2_score, 30);
        assert!(proved.labels.certificate_ref.is_some());
        assert!(proved.engine_cost_is_cpu);
        assert_eq!(proved.features.sat_conflicts, Some(7));

        let timeout =
            DatasetRow::from_record(&row("clean-smt", AttemptResult::Timeout, 9999, false), 5000);
        assert_eq!(timeout.labels.par2_score, 10000);
        assert!(timeout.labels.certificate_ref.is_none());
        assert_eq!(timeout.features.sat_conflicts, None);
    }

    #[test]
    fn test_oracle_cost_flagged_non_cpu() {
        let r = DatasetRow::from_record(&row("oracle", AttemptResult::Proved, 1200, false), 5000);
        assert!(
            !r.engine_cost_is_cpu,
            "oracle wall_ms is network latency, must be flagged non-CPU"
        );
    }

    #[test]
    fn test_export_jsonl_roundtrip_and_filter() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let out = tmp.path().join("ds.jsonl");
        let rows = vec![
            row("clean-smt", AttemptResult::Proved, 10, true),
            row("oracle", AttemptResult::Timeout, 5000, false),
        ];
        let n = export_jsonl(&rows, &ExportFilter::default(), 5000, &out).expect("export");
        assert_eq!(n, 2);
        let text = std::fs::read_to_string(&out).expect("read");
        assert_eq!(text.lines().count(), 2);
        // Each line must parse back into a DatasetRow.
        for line in text.lines() {
            let v: serde_json::Value = serde_json::from_str(line).expect("valid json line");
            assert!(v.get("features").is_some());
            assert!(v.get("labels").is_some());
            assert!(v.get("provenance").is_some());
        }

        // Engine filter keeps only the SMT row.
        let out2 = tmp.path().join("ds2.jsonl");
        let filter = ExportFilter {
            engine: Some("clean-smt".to_string()),
            theory: None,
        };
        let n2 = export_jsonl(&rows, &filter, 5000, &out2).expect("export filtered");
        assert_eq!(n2, 1, "engine filter keeps only clean-smt");
    }

    #[test]
    fn test_export_groups_by_obligation_keeps_losses() {
        // Both engines attempted the SAME obligation; the exporter must keep the
        // loss row (oracle timeout) so the consumer can reconstruct VBS/SBS.
        let tmp = tempfile::tempdir().expect("tempdir");
        let out = tmp.path().join("ds.jsonl");
        let rows = vec![
            row("clean-smt", AttemptResult::Proved, 10, true),
            row("oracle", AttemptResult::Timeout, 5000, false),
        ];
        export_jsonl(&rows, &ExportFilter::default(), 5000, &out).expect("export");
        let text = std::fs::read_to_string(&out).expect("read");
        let digests: Vec<String> = text
            .lines()
            .map(|l| {
                let v: serde_json::Value = serde_json::from_str(l).unwrap();
                v["provenance"]["obligation_digest"]
                    .as_str()
                    .unwrap()
                    .to_string()
            })
            .collect();
        assert_eq!(digests.len(), 2);
        assert_eq!(digests[0], digests[1], "siblings share obligation_digest");
    }
}
