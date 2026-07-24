// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Restart strategy verification for CDCL SAT solvers.
//!
//! Implements and verifies three restart strategies:
//! - **Luby**: Optimal among universal restart strategies (Luby, Sinclair, Zuckerman 1993)
//! - **Geometric**: Fixed-ratio growth (MiniSat-style)
//! - **Glucose**: LBD-based adaptive restarts (Audemard & Simon, IJCAI 2009)
//!
//! Proof obligations S07-S08 formalize correctness properties.

use crate::spec::ProofStatus;

/// S07: Restart preserves all decision-level-0 assignments (unit propagations).
///
/// ## Proof sketch:
/// A restart backtracks to decision level 0. All trail entries at level 0 are
/// unit propagations from the original clause set. Since clauses are never
/// removed during restart, these propagations remain valid. The trail prefix
/// at level 0 is therefore preserved.
pub const S07_RESTART_PRESERVES_TRAIL_PREFIX: ProofStatus = ProofStatus::DerivedPending;

/// S08: The Luby sequence is optimal among universal restart strategies.
///
/// ## Proof sketch (Luby, Sinclair, Zuckerman 1993, Theorem 1):
/// For any Las Vegas algorithm whose runtime distribution is unknown, the Luby
/// sequence minimizes the expected number of steps (up to a constant factor)
/// among all universal strategies (strategies that do not depend on the runtime
/// distribution). This is proven via a minimax argument over the space of
/// distributions.
pub const S08_LUBY_SEQUENCE_OPTIMAL: ProofStatus = ProofStatus::DerivedPending;

/// Restart strategy configuration.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum RestartStrategy {
    /// Luby sequence restart with a base conflict unit.
    Luby { unit: u64 },
    /// Geometric growth restart: threshold = base * factor^i.
    Geometric { base: u64, factor: f64 },
    /// Glucose-style LBD-based adaptive restart.
    Glucose { threshold_factor: f64 },
}

/// Statistics from restart frequency analysis.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct RestartStats {
    pub total_restarts: usize,
    pub mean_interval: f64,
    pub median_interval: f64,
    pub max_interval: u64,
}

/// Compute the i-th value of the Luby restart sequence (1-indexed).
///
/// The Luby sequence is defined recursively:
///   luby(i) = 2^(k-1)  if i == 2^k - 1
///   luby(i) = luby(i - 2^(k-1) + 1)  if 2^(k-1) <= i < 2^k - 1
///
/// Sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
///
/// Reference: Luby, Sinclair, Zuckerman, "Optimal Speedup of Las Vegas
/// Algorithms", Information Processing Letters 47(4), 1993.
#[must_use]
pub fn luby_sequence(i: usize) -> u64 {
    // Use 1-indexed position internally (the literature convention).
    let mut idx = i + 1;

    // Find the smallest complete binary tree size >= idx.
    // A complete tree of depth k has size 2^k - 1.
    let mut size: usize = 1;
    let mut seq: usize = 1;
    while size < idx {
        seq *= 2;
        size = 2 * size + 1;
    }
    // size = 2^k - 1 >= idx, seq = 2^(k-1)
    // Walk down the tree: if idx lands at the rightmost position, return seq.
    // Otherwise, recurse into the left subtree of size (size-1)/2.
    while size != idx {
        size = (size - 1) / 2;
        seq /= 2;
        if idx > size {
            idx -= size;
        }
    }
    seq as u64
}

/// Compute geometric restart threshold: base * factor^i.
///
/// Returns the conflict limit for the i-th restart in a geometric series.
/// Saturates at `u64::MAX` to avoid overflow.
#[must_use]
pub fn geometric_sequence(base: u64, factor: f64, i: usize) -> u64 {
    let threshold = (base as f64) * factor.powi(i as i32);
    if threshold >= u64::MAX as f64 {
        return u64::MAX;
    }
    if threshold < 1.0 {
        return 1;
    }
    threshold as u64
}

/// Compute the moving average of learned clause LBD values.
///
/// LBD (Literal Block Distance) counts the number of distinct decision levels
/// in a learned clause. Lower LBD indicates higher-quality clauses.
///
/// Returns 0.0 if `lbd_history` is empty or `window` is 0.
///
/// Reference: Audemard & Simon, "Predicting Learnt Clauses Quality in Modern
/// SAT Solvers", IJCAI 2009.
#[must_use]
pub fn glucose_lbd_average(lbd_history: &[u32], window: usize) -> f64 {
    if lbd_history.is_empty() || window == 0 {
        return 0.0;
    }
    let start = lbd_history.len().saturating_sub(window);
    let slice = &lbd_history[start..];
    let sum: u64 = slice.iter().map(|&v| u64::from(v)).sum();
    sum as f64 / slice.len() as f64
}

/// Decide whether to restart using the Luby strategy.
///
/// Restarts when the number of conflicts since the last restart reaches
/// `unit * luby_sequence(restart_count)`.
#[must_use]
pub fn should_restart_luby(conflicts: u64, unit: u64, restart_count: usize) -> bool {
    let threshold = unit.saturating_mul(luby_sequence(restart_count));
    conflicts >= threshold
}

/// Decide whether to restart using the Glucose LBD-based strategy.
///
/// Restarts when the recent LBD average exceeds `threshold_factor` times the
/// global LBD average. This triggers restarts when recently learned clauses
/// are of lower quality than the historical average.
///
/// Uses a window of the most recent 50 LBD values for the local average.
/// Returns `false` if there are fewer than 50 learned clauses (too early to judge).
#[must_use]
pub fn should_restart_glucose(lbd_history: &[u32], threshold_factor: f64) -> bool {
    const GLUCOSE_WINDOW: usize = 50;
    if lbd_history.len() < GLUCOSE_WINDOW {
        return false;
    }
    let global_avg = glucose_lbd_average(lbd_history, lbd_history.len());
    let local_avg = glucose_lbd_average(lbd_history, GLUCOSE_WINDOW);
    if global_avg <= 0.0 {
        return false;
    }
    local_avg > threshold_factor * global_avg
}

/// Verify that the first `n` values of a sequence match the Luby recursion.
///
/// Checks each value against `luby_sequence(i)`. Returns `true` if all match.
#[must_use]
pub fn verify_luby_property(seq: &[u64], n: usize) -> bool {
    let check_len = n.min(seq.len());
    (0..check_len).all(|i| seq[i] == luby_sequence(i))
}

/// Verify that a restart does not lose any clauses.
///
/// A correct restart implementation preserves the entire clause database.
/// This checks that every clause present before restart is still present after.
#[must_use]
pub fn verify_restart_preserves_clauses(
    clauses_before: &[Vec<i32>],
    clauses_after: &[Vec<i32>],
) -> bool {
    if clauses_after.len() < clauses_before.len() {
        return false;
    }
    // Every clause from before must appear in after (order may differ due to
    // learned clauses being appended, but originals must be retained).
    // Use sorted representations for comparison.
    let normalize = |c: &[i32]| {
        let mut s = c.to_vec();
        s.sort_unstable();
        s
    };
    let after_sorted: Vec<Vec<i32>> = clauses_after.iter().map(|c| normalize(c)).collect();
    clauses_before
        .iter()
        .all(|c| after_sorted.contains(&normalize(c)))
}

/// Analyze restart frequency from a sequence of conflict counts at each restart.
///
/// `conflict_counts` contains the cumulative conflict count at each restart point.
/// Returns statistics about the intervals between restarts.
#[must_use]
pub fn restart_frequency_analysis(conflict_counts: &[u64]) -> RestartStats {
    if conflict_counts.is_empty() {
        return RestartStats {
            total_restarts: 0,
            mean_interval: 0.0,
            median_interval: 0.0,
            max_interval: 0,
        };
    }
    if conflict_counts.len() == 1 {
        return RestartStats {
            total_restarts: 1,
            mean_interval: conflict_counts[0] as f64,
            median_interval: conflict_counts[0] as f64,
            max_interval: conflict_counts[0],
        };
    }
    let mut intervals: Vec<u64> = Vec::with_capacity(conflict_counts.len());
    intervals.push(conflict_counts[0]);
    for w in conflict_counts.windows(2) {
        intervals.push(w[1].saturating_sub(w[0]));
    }
    let total_restarts = conflict_counts.len();
    let sum: u64 = intervals.iter().sum();
    let mean_interval = sum as f64 / intervals.len() as f64;
    let max_interval = intervals.iter().copied().max().unwrap_or(0);

    let mut sorted = intervals;
    sorted.sort_unstable();
    let median_interval = if sorted.len().is_multiple_of(2) {
        let mid = sorted.len() / 2;
        (sorted[mid - 1] + sorted[mid]) as f64 / 2.0
    } else {
        sorted[sorted.len() / 2] as f64
    };

    RestartStats {
        total_restarts,
        mean_interval,
        median_interval,
        max_interval,
    }
}
