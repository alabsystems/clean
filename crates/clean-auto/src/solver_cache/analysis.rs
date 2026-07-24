// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weak-area / VBS-gap analysis over the solver telemetry stream (Phase 1).
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §5 and §6. Reads the
//! `solver-attempt-record-v1` rows captured by [`super::telemetry`] (one row per
//! solving attempt, written to `<dir>/attempts.jsonl`) and aggregates them along
//! the axes the design grounds in the SAT/SMT algorithm-selection literature:
//!
//! - **PAR-2** (penalised-average-runtime, factor 2): the canonical fused
//!   score — `wall_ms` if solved, else `2 × timeout_budget_ms`. Lower is better.
//! - **Per-solver / per-theory / per-strategy** slicing — the per-class slicing
//!   `discovery_stats.rs` does *not* do (the specific missing capability, §5).
//! - **VBS − SBS gap** (Rice 1976 → SATzilla): the *virtual best solver* (oracle
//!   that picks the best engine per instance) versus the *single best solver*
//!   (the one engine with the lowest aggregate PAR-2). The gap is the headroom a
//!   learned selector could capture; if small, Phase 3 should not be built.
//!
//! # Soundness
//!
//! This module is **pure telemetry analysis**: it never decides provability,
//! never serves a verdict, and has zero soundness weight. Aggregates are
//! effectiveness metrics only. A negative/timeout result is a budget-bounded
//! observation, never "unprovable" (design §2.4).

use std::collections::BTreeMap;
use std::path::Path;

use thiserror::Error;

use super::record::{AttemptResult, CacheOutcome, SolverAttemptRecord};

/// The PAR-2 penalty factor: an unsolved attempt scores `FACTOR × budget`.
const PAR_FACTOR: u64 = 2;

/// Default per-attempt timeout budget (ms) used for PAR-2 when a record carries
/// no explicit `resource_limit`. The Phase-0 record schema does not yet persist
/// the budget; this is the analysis-side assumption, surfaced in the report so
/// the score is interpretable. (5 s matches the design's example budget.)
pub(crate) const DEFAULT_TIMEOUT_BUDGET_MS: u64 = 5000;

/// Errors reading or parsing the telemetry stream.
#[derive(Debug, Error)]
pub(crate) enum AnalysisError {
    /// An I/O error reading an `attempts.jsonl` file.
    #[error("read telemetry {path}: {source}")]
    Io {
        /// Path of the telemetry file.
        path: String,
        /// Underlying I/O error.
        source: std::io::Error,
    },
}

/// Solver-failure taxonomy (design §5.1).
///
/// **Distinct from `FeedbackCategory`** (a kernel-rejection taxonomy). This
/// classifies why a *solving attempt* failed, derived from the attempt result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SolverFailureCategory {
    /// The attempt hit its resource budget.
    Timeout,
    /// The solver could not decide (incomplete / theory gap).
    Incomplete,
    /// A proof search ran but produced no replayable proof term.
    ReconstructionFailed,
    /// The solver reported a counter-model / satisfiable.
    CounterModel,
}

impl SolverFailureCategory {
    /// Classify a non-`Proved` attempt result. `Proved` is a success and is not
    /// a failure category (returns `None`).
    fn from_result(result: AttemptResult) -> Option<Self> {
        match result {
            AttemptResult::Proved => None,
            AttemptResult::Timeout => Some(Self::Timeout),
            AttemptResult::Unknown => Some(Self::Incomplete),
            AttemptResult::Noproof | AttemptResult::Unsat => Some(Self::ReconstructionFailed),
            AttemptResult::Sat => Some(Self::CounterModel),
        }
    }

    /// Stable label for tables / JSON.
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::Incomplete => "incomplete",
            Self::ReconstructionFailed => "reconstruction_failed",
            Self::CounterModel => "counter_model",
        }
    }
}

/// PAR-2 score for a single attempt: `wall_ms` if solved, else `FACTOR × budget`.
fn par2(result: AttemptResult, wall_ms: u64, budget_ms: u64) -> u64 {
    if result == AttemptResult::Proved {
        wall_ms
    } else {
        PAR_FACTOR.saturating_mul(budget_ms)
    }
}

/// Streaming accumulator for one aggregation class (a `(theory, solver)` pair, a
/// solver, a theory, or a strategy).
#[derive(Clone, Debug, Default)]
struct ClassAccumulator {
    attempts: u64,
    solved: u64,
    cache_hits: u64,
    par2_sum: u64,
    wall_samples: Vec<u64>,
    failures: BTreeMap<SolverFailureCategory, u64>,
}

impl ClassAccumulator {
    fn add(&mut self, result: AttemptResult, wall_ms: u64, cache_hit: bool, budget_ms: u64) {
        self.attempts += 1;
        if result == AttemptResult::Proved {
            self.solved += 1;
            self.wall_samples.push(wall_ms);
        } else if let Some(cat) = SolverFailureCategory::from_result(result) {
            *self.failures.entry(cat).or_insert(0) += 1;
        }
        if cache_hit {
            self.cache_hits += 1;
        }
        self.par2_sum = self
            .par2_sum
            .saturating_add(par2(result, wall_ms, budget_ms));
    }

    fn finish(mut self) -> ClassStats {
        self.wall_samples.sort_unstable();
        ClassStats {
            attempts: self.attempts,
            solved: self.solved,
            success_rate: ratio(self.solved, self.attempts),
            mean_par2: if self.attempts == 0 {
                0.0
            } else {
                self.par2_sum as f64 / self.attempts as f64
            },
            cache_hit_rate: ratio(self.cache_hits, self.attempts),
            wall_p50: percentile(&self.wall_samples, 50),
            wall_p90: percentile(&self.wall_samples, 90),
            wall_max: self.wall_samples.last().copied(),
            timeout_rate: ratio(
                self.failures
                    .get(&SolverFailureCategory::Timeout)
                    .copied()
                    .unwrap_or(0),
                self.attempts,
            ),
            failures: self
                .failures
                .into_iter()
                .map(|(c, n)| (c.label().to_string(), n))
                .collect(),
        }
    }
}

fn ratio(num: u64, den: u64) -> f64 {
    if den == 0 {
        0.0
    } else {
        num as f64 / den as f64
    }
}

/// Nearest-rank percentile over a *sorted* slice of samples (`None` if empty).
fn percentile(sorted: &[u64], pct: u8) -> Option<u64> {
    if sorted.is_empty() {
        return None;
    }
    // Nearest-rank: rank = ceil(pct/100 * n), 1-based.
    let n = sorted.len();
    let rank = (pct as usize * n).div_ceil(100);
    let idx = rank.saturating_sub(1).min(n - 1);
    Some(sorted[idx])
}

/// Aggregated stats for one class (solver / theory / strategy / pair).
#[derive(Clone, Debug, PartialEq, serde::Serialize)]
pub struct ClassStats {
    /// Total attempts in this class.
    pub attempts: u64,
    /// Attempts solved (`Proved`).
    pub solved: u64,
    /// `solved / attempts`.
    pub success_rate: f64,
    /// Mean PAR-2 over all attempts in the class (lower is better).
    pub mean_par2: f64,
    /// `cache_hits / attempts`.
    pub cache_hit_rate: f64,
    /// p50 wall time (ms) over solved attempts.
    pub wall_p50: Option<u64>,
    /// p90 wall time (ms) over solved attempts.
    pub wall_p90: Option<u64>,
    /// max wall time (ms) over solved attempts.
    pub wall_max: Option<u64>,
    /// `timeouts / attempts`.
    pub timeout_rate: f64,
    /// Per-`SolverFailureCategory` counts (sorted by label).
    pub failures: Vec<(String, u64)>,
}

/// The VBS − SBS gap report (design §6).
#[derive(Clone, Debug, PartialEq, serde::Serialize)]
pub struct VbsGapReport {
    /// Mean PAR-2 of the virtual best solver (best engine picked per obligation).
    pub vbs_mean_par2: f64,
    /// Name of the single best solver (lowest aggregate mean PAR-2).
    pub sbs_solver: String,
    /// Mean PAR-2 of the single best solver over the same obligation set.
    pub sbs_mean_par2: f64,
    /// `sbs_mean_par2 - vbs_mean_par2` — the headroom a per-instance selector
    /// could capture. Zero/near-zero ⇒ a learned selector is not worth building.
    pub gap: f64,
    /// Distinct obligations that contributed to the gap.
    pub obligations: u64,
}

/// The full aggregation result over a telemetry stream.
#[derive(Clone, Debug, serde::Serialize)]
pub struct AggregateReport {
    /// Total attempt rows read.
    pub total_attempts: u64,
    /// Distinct obligations seen.
    pub distinct_obligations: u64,
    /// The PAR-2 timeout budget (ms) the scores assume.
    pub budget_ms: u64,
    /// Per-solver stats, keyed by solver name (sorted).
    pub by_solver: Vec<(String, ClassStats)>,
    /// Per-theory stats, keyed by `theory_logic` (sorted).
    pub by_theory: Vec<(String, ClassStats)>,
    /// Per-strategy stats, keyed by `strategy` (sorted).
    pub by_strategy: Vec<(String, ClassStats)>,
    /// VBS − SBS gap over the whole stream.
    pub vbs_gap: VbsGapReport,
}

/// How attempts are grouped for the `weak` worklist (design §5.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WeakBy {
    /// Group by `theory_logic`.
    Theory,
    /// Group by `solver_name`.
    Solver,
    /// Group by `(theory_logic, solver_name)` pair.
    TheorySolver,
}

/// Read every `solver-attempt-record-v1` row from one `attempts.jsonl` file.
///
/// Lines that fail to parse are skipped (forward/back compat with schema drift);
/// the line count of skips is not currently surfaced (Phase 1 keeps the reader
/// permissive). Returns the parsed rows in file order.
pub(crate) fn read_attempts(path: &Path) -> Result<Vec<SolverAttemptRecord>, AnalysisError> {
    let text = std::fs::read_to_string(path).map_err(|e| AnalysisError::Io {
        path: path.display().to_string(),
        source: e,
    })?;
    let rows = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|line| serde_json::from_str::<SolverAttemptRecord>(line).ok())
        .collect();
    Ok(rows)
}

/// Read + concatenate attempt rows from `<dir>/attempts.jsonl` for each dir.
///
/// A missing `attempts.jsonl` in a directory contributes no rows (not an error);
/// an unreadable-but-present file is an error.
pub(crate) fn read_attempts_from_dirs(
    dirs: &[&Path],
) -> Result<Vec<SolverAttemptRecord>, AnalysisError> {
    let mut all = Vec::new();
    for dir in dirs {
        let path = dir.join("attempts.jsonl");
        if path.exists() {
            all.extend(read_attempts(&path)?);
        }
    }
    Ok(all)
}

/// Aggregate a slice of attempt rows into the full report.
///
/// `budget_ms` is the PAR-2 timeout budget (use [`DEFAULT_TIMEOUT_BUDGET_MS`]
/// when no per-record budget is available — the Phase-0 schema does not persist
/// it yet).
pub(crate) fn aggregate(rows: &[SolverAttemptRecord], budget_ms: u64) -> AggregateReport {
    let mut by_solver: BTreeMap<String, ClassAccumulator> = BTreeMap::new();
    let mut by_theory: BTreeMap<String, ClassAccumulator> = BTreeMap::new();
    let mut by_strategy: BTreeMap<String, ClassAccumulator> = BTreeMap::new();
    // For VBS/SBS: per (obligation, solver) min PAR-2, plus per-solver totals.
    let mut per_oblig_solver: BTreeMap<(String, String), u64> = BTreeMap::new();
    let mut distinct: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

    for r in rows {
        let cache_hit = r.cache_outcome == CacheOutcome::CacheHit;
        let p = par2(r.result, r.wall_ms, budget_ms);
        by_solver
            .entry(r.solver.name.clone())
            .or_default()
            .add(r.result, r.wall_ms, cache_hit, budget_ms);
        by_theory
            .entry(r.theory_logic.clone())
            .or_default()
            .add(r.result, r.wall_ms, cache_hit, budget_ms);
        by_strategy
            .entry(r.strategy.clone())
            .or_default()
            .add(r.result, r.wall_ms, cache_hit, budget_ms);
        distinct.insert(r.obligation_digest.clone());
        let key = (r.obligation_digest.clone(), r.solver.name.clone());
        let slot = per_oblig_solver.entry(key).or_insert(u64::MAX);
        *slot = (*slot).min(p);
    }

    let vbs_gap = compute_vbs_gap(&per_oblig_solver);

    AggregateReport {
        total_attempts: rows.len() as u64,
        distinct_obligations: distinct.len() as u64,
        budget_ms,
        by_solver: finish_map(by_solver),
        by_theory: finish_map(by_theory),
        by_strategy: finish_map(by_strategy),
        vbs_gap,
    }
}

fn finish_map(map: BTreeMap<String, ClassAccumulator>) -> Vec<(String, ClassStats)> {
    map.into_iter().map(|(k, acc)| (k, acc.finish())).collect()
}

/// Compute the VBS − SBS gap from per-`(obligation, solver)` best PAR-2 scores.
///
/// - **VBS**: for each obligation, take the min PAR-2 across solvers; the VBS
///   mean is the average of those per-obligation minima.
/// - **SBS**: for each solver, its mean PAR-2 over *all* obligations (an
///   obligation the solver never attempted scores the timeout penalty for that
///   solver — the standard ASlib convention so a missing engine is a loss, not a
///   skip). The SBS is the solver with the lowest such mean.
fn compute_vbs_gap(per_oblig_solver: &BTreeMap<(String, String), u64>) -> VbsGapReport {
    use std::collections::{BTreeMap as Map, BTreeSet as Set};
    let mut obligs: Set<&str> = Set::new();
    let mut solvers: Set<&str> = Set::new();
    let mut best: Map<(&str, &str), u64> = Map::new();
    for ((o, s), p) in per_oblig_solver {
        obligs.insert(o.as_str());
        solvers.insert(s.as_str());
        best.insert((o.as_str(), s.as_str()), *p);
    }
    if obligs.is_empty() {
        return VbsGapReport {
            vbs_mean_par2: 0.0,
            sbs_solver: String::new(),
            sbs_mean_par2: 0.0,
            gap: 0.0,
            obligations: 0,
        };
    }

    // VBS: per-obligation min over solvers.
    let mut vbs_sum = 0u64;
    for o in &obligs {
        let oblig_min = solvers
            .iter()
            .filter_map(|s| best.get(&(*o, *s)).copied())
            .min()
            .unwrap_or(u64::MAX);
        vbs_sum = vbs_sum.saturating_add(oblig_min);
    }
    let n = obligs.len() as u64;
    let vbs_mean = vbs_sum as f64 / n as f64;

    // SBS: per-solver mean over ALL obligations (missing = penalty = its own
    // worst observed, falling back to the global max penalty). We use the
    // largest PAR-2 the solver itself produced as the per-solver penalty; if it
    // never produced one, fall back to the global max.
    let global_max = best.values().copied().max().unwrap_or(0);
    let mut sbs_solver = String::new();
    let mut sbs_mean = f64::INFINITY;
    for s in &solvers {
        let solver_max = obligs
            .iter()
            .filter_map(|o| best.get(&(*o, *s)).copied())
            .max()
            .unwrap_or(global_max)
            .max(global_max);
        let sum: u64 = obligs
            .iter()
            .map(|o| best.get(&(*o, *s)).copied().unwrap_or(solver_max))
            .fold(0u64, |a, b| a.saturating_add(b));
        let mean = sum as f64 / n as f64;
        if mean < sbs_mean {
            sbs_mean = mean;
            sbs_solver = (*s).to_string();
        }
    }
    if !sbs_mean.is_finite() {
        sbs_mean = vbs_mean;
    }

    VbsGapReport {
        vbs_mean_par2: vbs_mean,
        sbs_solver,
        sbs_mean_par2: sbs_mean,
        gap: (sbs_mean - vbs_mean).max(0.0),
        obligations: n,
    }
}

/// Build the weak-area worklist: classes sorted worst-first by mean PAR-2
/// (ties broken by lower success rate). Returns at most `top` entries.
pub(crate) fn weak_areas(
    rows: &[SolverAttemptRecord],
    by: WeakBy,
    budget_ms: u64,
    top: usize,
) -> Vec<(String, ClassStats)> {
    let mut map: BTreeMap<String, ClassAccumulator> = BTreeMap::new();
    for r in rows {
        let cache_hit = r.cache_outcome == CacheOutcome::CacheHit;
        let key = match by {
            WeakBy::Theory => r.theory_logic.clone(),
            WeakBy::Solver => r.solver.name.clone(),
            WeakBy::TheorySolver => format!("{} / {}", r.theory_logic, r.solver.name),
        };
        map.entry(key)
            .or_default()
            .add(r.result, r.wall_ms, cache_hit, budget_ms);
    }
    let mut classes: Vec<(String, ClassStats)> = finish_map(map);
    classes.sort_by(|a, b| {
        b.1.mean_par2
            .partial_cmp(&a.1.mean_par2)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(
                a.1.success_rate
                    .partial_cmp(&b.1.success_rate)
                    .unwrap_or(std::cmp::Ordering::Equal),
            )
    });
    classes.truncate(top);
    classes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_cache::record::{SolverIdentity, SCHEMA_ID};

    fn row(
        oblig: &str,
        solver: &str,
        theory: &str,
        result: AttemptResult,
        wall_ms: u64,
    ) -> SolverAttemptRecord {
        SolverAttemptRecord {
            schema: SCHEMA_ID.to_string(),
            obligation_digest: format!("blake3:{}", oblig.repeat(64 / oblig.len().max(1))),
            theory_logic: theory.to_string(),
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
    fn test_par2_solved_uses_walltime() {
        assert_eq!(par2(AttemptResult::Proved, 42, 5000), 42);
    }

    #[test]
    fn test_par2_unsolved_uses_2x_budget() {
        assert_eq!(par2(AttemptResult::Timeout, 9999, 5000), 10000);
        assert_eq!(par2(AttemptResult::Unknown, 0, 5000), 10000);
    }

    #[test]
    fn test_percentile_nearest_rank() {
        let s = [10u64, 20, 30, 40, 50];
        assert_eq!(percentile(&s, 50), Some(30));
        assert_eq!(percentile(&s, 90), Some(50));
        assert_eq!(percentile(&[], 50), None);
        assert_eq!(percentile(&[7], 50), Some(7));
    }

    #[test]
    fn test_failure_category_mapping() {
        assert_eq!(
            SolverFailureCategory::from_result(AttemptResult::Proved),
            None
        );
        assert_eq!(
            SolverFailureCategory::from_result(AttemptResult::Timeout),
            Some(SolverFailureCategory::Timeout)
        );
        assert_eq!(
            SolverFailureCategory::from_result(AttemptResult::Sat),
            Some(SolverFailureCategory::CounterModel)
        );
    }

    #[test]
    fn test_aggregate_counts_and_rates() {
        let rows = vec![
            row("a", "clean-smt", "clean-cic", AttemptResult::Proved, 10),
            row("a", "clean-smt", "clean-cic", AttemptResult::Timeout, 5000),
            row("b", "oracle", "oracle", AttemptResult::Proved, 100),
        ];
        let rep = aggregate(&rows, 5000);
        assert_eq!(rep.total_attempts, 3);
        assert_eq!(rep.distinct_obligations, 2);

        let smt = &rep
            .by_solver
            .iter()
            .find(|(k, _)| k == "clean-smt")
            .expect("smt class")
            .1;
        assert_eq!(smt.attempts, 2);
        assert_eq!(smt.solved, 1);
        assert!((smt.success_rate - 0.5).abs() < 1e-9);
        // mean PAR-2 = (10 + 10000) / 2 = 5005.
        assert!((smt.mean_par2 - 5005.0).abs() < 1e-9);
        assert!((smt.timeout_rate - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_cache_hit_rate() {
        let mut r = row("a", "clean-smt", "clean-cic", AttemptResult::Proved, 1);
        r.cache_outcome = CacheOutcome::CacheHit;
        let rows = vec![
            r,
            row("a", "clean-smt", "clean-cic", AttemptResult::Proved, 50),
        ];
        let rep = aggregate(&rows, 5000);
        let smt = &rep.by_solver[0].1;
        assert!((smt.cache_hit_rate - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_vbs_gap_zero_when_one_solver() {
        // One solver ⇒ VBS == SBS ⇒ gap 0.
        let rows = vec![
            row("a", "clean-smt", "clean-cic", AttemptResult::Proved, 10),
            row("b", "clean-smt", "clean-cic", AttemptResult::Timeout, 5000),
        ];
        let rep = aggregate(&rows, 5000);
        assert!(rep.vbs_gap.gap.abs() < 1e-9, "single solver ⇒ no gap");
        assert_eq!(rep.vbs_gap.sbs_solver, "clean-smt");
    }

    #[test]
    fn test_vbs_gap_positive_when_engines_complement() {
        // smt solves `a` fast but times out on `b`; oracle is the reverse.
        // VBS picks the winner each time (10, 20) ⇒ mean 15.
        // Each solver alone: smt = (10 + 10000)/2 = 5005; oracle = (10000+20)/2 = 5010.
        // SBS = smt @ 5005 ⇒ gap = 5005 - 15 = 4990 > 0.
        let rows = vec![
            row("a", "clean-smt", "clean-cic", AttemptResult::Proved, 10),
            row("b", "clean-smt", "clean-cic", AttemptResult::Timeout, 5000),
            row("a", "oracle", "oracle", AttemptResult::Timeout, 5000),
            row("b", "oracle", "oracle", AttemptResult::Proved, 20),
        ];
        let rep = aggregate(&rows, 5000);
        assert!(
            (rep.vbs_gap.vbs_mean_par2 - 15.0).abs() < 1e-9,
            "vbs mean = {}",
            rep.vbs_gap.vbs_mean_par2
        );
        assert!(rep.vbs_gap.gap > 4000.0, "gap = {}", rep.vbs_gap.gap);
        assert_eq!(rep.vbs_gap.sbs_solver, "clean-smt");
        assert_eq!(rep.vbs_gap.obligations, 2);
    }

    #[test]
    fn test_weak_areas_worst_first() {
        let rows = vec![
            // theory X: always solved fast (good).
            row("a", "clean-smt", "X", AttemptResult::Proved, 5),
            row("b", "clean-smt", "X", AttemptResult::Proved, 5),
            // theory Y: always times out (bad — should rank first).
            row("c", "clean-smt", "Y", AttemptResult::Timeout, 5000),
            row("d", "clean-smt", "Y", AttemptResult::Timeout, 5000),
        ];
        let weak = weak_areas(&rows, WeakBy::Theory, 5000, 10);
        assert_eq!(weak.len(), 2);
        assert_eq!(weak[0].0, "Y", "worst PAR-2 theory ranks first");
        assert!(weak[0].1.mean_par2 > weak[1].1.mean_par2);
    }
}
