// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public orchestration surface for the Phase-1 solver-cache tooling.
//!
//! This is the API the `clean solver` CLI (`clean-cli`) drives. It ties the
//! internal Phase-0/1 modules together:
//!
//! - [`build_index`] — fold telemetry rows + cache membership over a set of
//!   directories into a [`super::index::SolverIndex`] (`VCIDX01`), pinned to a
//!   `corpus_digest` over the source bytes.
//! - [`stats`] / [`weak`] / [`vbs_gap`] — the analysis reports (design §5/§6).
//! - [`export_dataset`] — the NN training-data exporter (design §6.3).
//!
//! Everything here is **pure tooling over the telemetry stream**: zero kernel
//! interaction, zero soundness weight (design §5, §6). The index is a lookup
//! accelerator, never an arbiter.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use thiserror::Error;

use super::analysis::{
    self, AggregateReport, ClassStats, VbsGapReport, WeakBy, DEFAULT_TIMEOUT_BUDGET_MS,
};
use super::dataset::{self, ExportFilter};
use super::index::{self, SolverIndex, SummaryAccumulator};
use super::record::{AttemptResult, SolverAttemptRecord};
use super::store;
use super::telemetry;

/// Re-export the telemetry-analysis error type used by [`ServiceError`].
pub use super::analysis::AnalysisError;
/// Re-export the weak-area grouping axis for CLI callers.
pub use super::analysis::WeakBy as WeakArea;
/// Re-export aggregate / class / gap report types for CLI rendering.
pub use super::analysis::{
    AggregateReport as StatsReport, ClassStats as ClassReport, VbsGapReport as GapReport,
};
/// Re-export the dataset-export error type used by [`ServiceError`].
pub use super::dataset::DatasetError;
/// Re-export the dataset export filter for CLI callers.
pub use super::dataset::ExportFilter as DatasetFilter;
/// Re-export the index error type used by [`ServiceError`].
pub use super::index::IndexError;
/// Re-export the loaded index type for CLI lookups.
pub use super::index::SolverIndex as Index;

// ── Phase-2 service surface (transport-agnostic dispatch + ingest) ──────────
/// Encode a kernel proof term into the ingest `proof_term_hex` form (tools/tests).
pub use super::ingest::encode_proof_hex;
/// The transport-agnostic request dispatcher (design §10.2). The `solver_serve`
/// binary's raw-`tokio` HTTP shell and `clean-cli`'s integration tests both
/// drive this.
pub use super::serve::{
    dispatch, ApiResponse, ServeApiError, ServeState, SERVICE_NAME, TRUST_NOTE,
};
/// The crate error type, surfaced here so external callers of the public
/// [`encode_proof_hex`] helper (which returns it) can name + match on it.
pub use super::SolverCacheError;

/// Errors from the public solver-cache service surface.
#[derive(Debug, Error)]
pub enum ServiceError {
    /// Reading the telemetry stream failed.
    #[error(transparent)]
    Analysis(#[from] AnalysisError),
    /// Building or loading the `VCIDX01` index failed.
    #[error(transparent)]
    Index(#[from] IndexError),
    /// Exporting the NN dataset failed.
    #[error(transparent)]
    Dataset(#[from] DatasetError),
}

/// Summary returned after building a `VCIDX01` index.
#[derive(Clone, Debug)]
pub struct BuildSummary {
    /// Number of obligations (unique digests) indexed.
    pub entries: u64,
    /// Total attempt rows folded in.
    pub attempts: u64,
    /// Obligations with a re-checkable proof term in the cache dirs.
    pub cached: u64,
    /// `blake3:<hex>` corpus digest pinned in the index header.
    pub corpus_digest: String,
    /// Bytes written to the index file.
    pub index_bytes: u64,
}

/// The telemetry budget the reports use (ms). Phase-0 records do not persist the
/// per-attempt budget, so this is the analysis-side assumption (surfaced in
/// reports). See [`analysis::DEFAULT_TIMEOUT_BUDGET_MS`].
#[must_use]
pub fn default_budget_ms() -> u64 {
    DEFAULT_TIMEOUT_BUDGET_MS
}

/// Read all attempt rows from the `attempts.jsonl` files under `dirs`.
fn read_rows(dirs: &[PathBuf]) -> Result<Vec<SolverAttemptRecord>, ServiceError> {
    let refs: Vec<&Path> = dirs.iter().map(PathBuf::as_path).collect();
    Ok(analysis::read_attempts_from_dirs(&refs)?)
}

/// Compute the corpus-pin digest over the source inputs in a deterministic
/// order: every `attempts.jsonl` then every `.scache` record, hashed in
/// sorted-path order (mirroring `MVBIDX01`'s sorted-path corpus pin).
fn corpus_digest(dirs: &[PathBuf]) -> [u8; 32] {
    let mut paths: Vec<PathBuf> = Vec::new();
    for dir in dirs {
        let attempts = dir.join("attempts.jsonl");
        if attempts.exists() {
            paths.push(attempts);
        }
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.extension().and_then(|e| e.to_str()) == Some("scache") {
                    paths.push(p);
                }
            }
        }
    }
    paths.sort();
    paths.dedup();
    let mut hasher = blake3::Hasher::new();
    for p in &paths {
        if let Ok(bytes) = std::fs::read(p) {
            // Length-prefix each file so concatenation is unambiguous.
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
    }
    *hasher.finalize().as_bytes()
}

/// Build a `VCIDX01` index over the telemetry + cache directories `dirs`,
/// writing it to `out`. Returns a [`BuildSummary`].
///
/// Folds every attempt row into a per-obligation [`SummaryAccumulator`] and
/// marks `cached = true` for any obligation with a `.scache` proof term in a
/// directory. The index is pinned to a `corpus_digest` over the source bytes.
///
/// # Errors
///
/// Telemetry read failures or index-write I/O failures.
pub fn build_index(dirs: &[PathBuf], out: &Path) -> Result<BuildSummary, ServiceError> {
    let rows = read_rows(dirs)?;
    let mut accs: BTreeMap<String, SummaryAccumulator> = BTreeMap::new();
    for r in &rows {
        accs.entry(r.obligation_digest.clone())
            .or_default()
            .add_attempt(r.result == AttemptResult::Proved, r.wall_ms);
    }
    // Mark cache membership from the `.scache` files in each dir.
    let mut cached = 0u64;
    for dir in dirs {
        for digest in store::cached_digests(dir) {
            let acc = accs.entry(digest).or_default();
            acc.mark_cached();
            cached += 1;
        }
    }
    let corpus = corpus_digest(dirs);
    let entries = index::build_index(&accs, &corpus, out)?;
    let index_bytes = std::fs::metadata(out).map(|m| m.len()).unwrap_or(0);
    Ok(BuildSummary {
        entries,
        attempts: rows.len() as u64,
        cached,
        corpus_digest: index::key_digest(&corpus),
        index_bytes,
    })
}

/// Load a `VCIDX01` index (fail-closed) from `path`.
///
/// # Errors
///
/// Any structural inconsistency or self-digest mismatch in the index file.
pub fn load_index(path: &Path) -> Result<SolverIndex, ServiceError> {
    Ok(SolverIndex::load(path)?)
}

/// Aggregate the telemetry stream under `dirs` into the full stats report.
///
/// # Errors
///
/// Telemetry read failures.
pub fn stats(dirs: &[PathBuf], budget_ms: u64) -> Result<AggregateReport, ServiceError> {
    let rows = read_rows(dirs)?;
    Ok(analysis::aggregate(&rows, budget_ms))
}

/// The weak-area worklist (worst classes first) for the telemetry under `dirs`.
///
/// # Errors
///
/// Telemetry read failures.
pub fn weak(
    dirs: &[PathBuf],
    by: WeakBy,
    budget_ms: u64,
    top: usize,
) -> Result<Vec<(String, ClassStats)>, ServiceError> {
    let rows = read_rows(dirs)?;
    Ok(analysis::weak_areas(&rows, by, budget_ms, top))
}

/// The VBS − SBS gap report for the telemetry under `dirs`.
///
/// # Errors
///
/// Telemetry read failures.
pub fn vbs_gap(dirs: &[PathBuf], budget_ms: u64) -> Result<VbsGapReport, ServiceError> {
    let rows = read_rows(dirs)?;
    Ok(analysis::aggregate(&rows, budget_ms).vbs_gap)
}

/// Export the NN training dataset for the telemetry under `dirs` to `out`.
/// Returns the number of rows written.
///
/// # Errors
///
/// Telemetry read or dataset-write failures.
pub fn export_dataset(
    dirs: &[PathBuf],
    filter: &ExportFilter,
    budget_ms: u64,
    out: &Path,
) -> Result<u64, ServiceError> {
    let rows = read_rows(dirs)?;
    Ok(dataset::export_jsonl(&rows, filter, budget_ms, out)?)
}

/// The telemetry filename appended within a telemetry directory.
#[must_use]
pub fn attempts_filename() -> &'static str {
    "attempts.jsonl"
}

/// Re-export the env var names so callers can default `dirs` from the
/// environment (mirroring how the producer side is configured).
#[must_use]
pub fn telemetry_dir_env() -> &'static str {
    telemetry::TELEMETRY_DIR_ENV
}

/// The cache-dir env var name.
#[must_use]
pub fn cache_dir_env() -> &'static str {
    store::CACHE_DIR_ENV
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_cache::record::{CacheOutcome, SolverIdentity, SCHEMA_ID};
    use std::io::Write as _;

    fn write_attempts(dir: &Path, rows: &[SolverAttemptRecord]) {
        std::fs::create_dir_all(dir).expect("mkdir");
        let path = dir.join("attempts.jsonl");
        let mut f = std::fs::File::create(path).expect("create");
        for r in rows {
            writeln!(f, "{}", r.to_jsonl().expect("ser")).expect("write");
        }
    }

    fn row(
        oblig_hex: u8,
        solver: &str,
        result: AttemptResult,
        wall_ms: u64,
    ) -> SolverAttemptRecord {
        SolverAttemptRecord {
            schema: SCHEMA_ID.to_string(),
            obligation_digest: format!("blake3:{}", format!("{oblig_hex:02x}").repeat(32)),
            theory_logic: "clean-cic".to_string(),
            solver: SolverIdentity {
                name: solver.to_string(),
                version: "test".to_string(),
            },
            strategy: "smt→superposition→oracle".to_string(),
            result,
            wall_ms,
            success: result == AttemptResult::Proved,
            proof_term_digest: (result == AttemptResult::Proved)
                .then(|| "blake3:".to_string() + &"cd".repeat(32)),
            smt_stats: None,
            cache_outcome: CacheOutcome::Miss,
            decided_at_epoch_s: 1_750_000_000,
        }
    }

    #[test]
    fn test_build_index_folds_attempts_and_loads() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("tele");
        write_attempts(
            &dir,
            &[
                row(0xaa, "clean-smt", AttemptResult::Proved, 30),
                row(0xaa, "oracle", AttemptResult::Timeout, 5000),
                row(0xbb, "clean-smt", AttemptResult::Proved, 12),
            ],
        );
        let out = tmp.path().join("solver.vcidx");
        let summary = build_index(std::slice::from_ref(&dir), &out).expect("build");
        assert_eq!(summary.entries, 2, "two distinct obligations");
        assert_eq!(summary.attempts, 3);

        let index = load_index(&out).expect("load fail-closed");
        let aa = format!("blake3:{}", "aa".repeat(32));
        let s = index.lookup(&aa).expect("hit aa");
        assert_eq!(s.attempts, 2);
        assert_eq!(s.solved, 1);
        assert_eq!(s.best_wall_ms, Some(30));
    }

    #[test]
    fn test_build_index_corpus_pin_is_stable() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("tele");
        write_attempts(&dir, &[row(0xaa, "clean-smt", AttemptResult::Proved, 30)]);
        let out1 = tmp.path().join("a.vcidx");
        let out2 = tmp.path().join("b.vcidx");
        let s1 = build_index(std::slice::from_ref(&dir), &out1).expect("build 1");
        let s2 = build_index(std::slice::from_ref(&dir), &out2).expect("build 2");
        assert_eq!(
            s1.corpus_digest, s2.corpus_digest,
            "same inputs ⇒ same corpus pin"
        );
        // Byte-identical index files (deterministic build).
        assert_eq!(
            std::fs::read(&out1).unwrap(),
            std::fs::read(&out2).unwrap(),
            "deterministic index bytes"
        );
    }

    #[test]
    fn test_stats_over_dirs() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("tele");
        write_attempts(
            &dir,
            &[
                row(0xaa, "clean-smt", AttemptResult::Proved, 30),
                row(0xbb, "clean-smt", AttemptResult::Timeout, 5000),
            ],
        );
        let rep = stats(&[dir], 5000).expect("stats");
        assert_eq!(rep.total_attempts, 2);
        assert_eq!(rep.by_solver.len(), 1);
        assert_eq!(rep.by_solver[0].0, "clean-smt");
    }

    #[test]
    fn test_missing_telemetry_dir_is_empty_not_error() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().join("does-not-exist");
        let rep = stats(&[dir], 5000).expect("missing dir ⇒ empty, not error");
        assert_eq!(rep.total_attempts, 0);
    }
}
