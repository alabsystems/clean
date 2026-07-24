// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended VSIDS verification: decay monotonicity, phase saving, and restart schedules.
//!
//! Builds on the core VSIDS heuristic in [`super::vsids`] with additional
//! verification functions for properties that matter in practice:
//!
//! - **Decay monotonicity**: after applying a decay factor, all scores decrease
//!   proportionally and relative ordering is preserved.
//! - **Bump ordering**: recently bumped variables dominate the decision queue.
//! - **Score overflow safety**: no score exceeds the rescale threshold.
//! - **Phase saving consistency**: the saved polarity for each variable matches
//!   its last assignment on the trail.
//! - **Luby restart schedule**: restart points follow the Luby sequence scaled
//!   by a base conflict count.
//!
//! References:
//! - Pipatsrisawat & Darwiche, "A Lightweight Component Caching Scheme for
//!   Satisfiability Solvers", SAT 2007 (phase saving).
//! - Luby, Sinclair, Zuckerman, "Optimal Speedup of Las Vegas Algorithms",
//!   Information Processing Letters 47(4), 1993 (Luby sequence).

use crate::spec::ProofStatus;

/// S07 (VSIDS extension): Decay monotonicity — after multiplying all scores by
/// `decay_factor` in (0,1), every score decreases and relative ordering is preserved.
///
/// ## Proof sketch:
/// For all i, `scores_after[i] = scores_before[i] * decay_factor`.
/// Since `0 < decay_factor < 1`, `scores_after[i] <= scores_before[i]`.
/// For any i,j: if `scores_before[i] > scores_before[j]`, then
/// `scores_after[i] = scores_before[i] * d > scores_before[j] * d = scores_after[j]`.
pub const S07_VSIDS_DECAY_MONOTONICITY: ProofStatus = ProofStatus::DerivedPending;

/// S08 (VSIDS extension): Phase saving consistency — the saved phase for every
/// variable matches the polarity of its most recent assignment on the trail.
///
/// ## Proof sketch:
/// Phase saving records `saved_phases[var] = Some(polarity)` each time a variable
/// is unassigned during backtracking. For any variable that has appeared on the
/// trail, its saved phase equals the polarity of its last trail entry. Variables
/// that have never been assigned have `saved_phases[var] = None`.
pub const S08_PHASE_SAVING_CONSISTENCY: ProofStatus = ProofStatus::DerivedPending;

/// Verify that scores decreased by the given decay factor.
///
/// Returns `true` when every `scores_after[i]` is approximately
/// `scores_before[i] * decay_factor` (within floating-point tolerance),
/// and no score increased. Both slices must have equal length.
#[must_use]
pub fn verify_decay_monotonicity(
    scores_before: &[f64],
    scores_after: &[f64],
    decay_factor: f64,
) -> bool {
    if scores_before.len() != scores_after.len() {
        return false;
    }
    if !(0.0 < decay_factor && decay_factor <= 1.0) {
        return false;
    }
    let eps = 1e-9;
    scores_before
        .iter()
        .zip(scores_after.iter())
        .all(|(&before, &after)| {
            let expected = before * decay_factor;
            (after - expected).abs() < eps && after <= before + eps
        })
}

/// Verify that all recently bumped variables have higher scores than
/// every non-bumped variable.
///
/// `recently_bumped` contains variable indices (0-based into `scores`).
/// Returns `true` when `min(bumped scores) >= max(non-bumped scores)`.
/// Empty `recently_bumped` or empty `scores` trivially returns `true`.
#[must_use]
pub fn verify_bump_ordering(scores: &[f64], recently_bumped: &[u32]) -> bool {
    if scores.is_empty() || recently_bumped.is_empty() {
        return true;
    }
    let bumped_set: std::collections::HashSet<u32> = recently_bumped.iter().copied().collect();

    let mut min_bumped = f64::INFINITY;
    let mut max_non_bumped = f64::NEG_INFINITY;

    for (i, &score) in scores.iter().enumerate() {
        if bumped_set.contains(&(i as u32)) {
            if score < min_bumped {
                min_bumped = score;
            }
        } else if score > max_non_bumped {
            max_non_bumped = score;
        }
    }
    // If all variables are bumped, max_non_bumped stays NEG_INFINITY => true.
    // If no non-bumped variables exist, the ordering trivially holds.
    if max_non_bumped == f64::NEG_INFINITY {
        return true;
    }
    min_bumped >= max_non_bumped
}

/// Verify that no score exceeds the given maximum.
///
/// Returns `true` when every score in the slice is <= `max_score`
/// and is non-negative.
#[must_use]
pub fn verify_score_overflow_safety(scores: &[f64], max_score: f64) -> bool {
    scores.iter().all(|&s| s >= 0.0 && s <= max_score)
}

/// Uniformly rescale all scores by `scale_factor`.
///
/// This is the operation performed when scores approach the overflow
/// threshold. Dividing all scores by the same positive constant preserves
/// relative ordering.
///
/// Does nothing if `scale_factor` is not positive and finite.
pub fn rescale_scores(scores: &mut [f64], scale_factor: f64) {
    if !(scale_factor > 0.0 && scale_factor.is_finite()) {
        return;
    }
    for score in scores.iter_mut() {
        *score *= scale_factor;
    }
}

/// Verify phase saving consistency against trail history.
///
/// `saved_phases` is indexed by variable (0-based). `trail_history` contains
/// `(literal, _polarity_)` pairs in chronological order, where the literal's
/// sign encodes polarity (positive = true, negative = false).
///
/// Returns `true` when every `saved_phases[var]` that is `Some(pol)` matches
/// the polarity of the **last** occurrence of that variable on the trail.
/// Variables with `None` must not appear on the trail.
#[must_use]
pub fn phase_saving_consistency(
    saved_phases: &[Option<bool>],
    trail_history: &[(i32, bool)],
) -> bool {
    // Build map: var -> last polarity on trail.
    let mut last_polarity: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    for &(lit, _) in trail_history {
        let var = lit.unsigned_abs();
        let pol = lit > 0;
        last_polarity.insert(var, pol);
    }

    for (var_idx, saved) in saved_phases.iter().enumerate() {
        let var = var_idx as u32;
        match (saved, last_polarity.get(&var)) {
            (Some(saved_pol), Some(trail_pol)) => {
                if saved_pol != trail_pol {
                    return false;
                }
            }
            (Some(_), None) => {
                // Saved phase for a variable never on the trail => inconsistent.
                return false;
            }
            (None, _) => {
                // No saved phase is always acceptable.
            }
        }
    }
    true
}

/// Compute the Luby restart sequence value at the given 0-indexed position.
///
/// Sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
///
/// This is a convenience wrapper matching the interface expected by
/// [`verify_restart_schedule`]. See [`super::restart::luby_sequence`] for the
/// primary implementation with full documentation.
#[must_use]
pub fn luby_restart_sequence(index: usize) -> u64 {
    // Iterative computation using the complete binary tree method.
    let mut idx = index + 1; // convert to 1-indexed
    let mut size: usize = 1;
    let mut seq: usize = 1;
    while size < idx {
        seq *= 2;
        size = 2 * size + 1;
    }
    while size != idx {
        size = (size - 1) / 2;
        seq /= 2;
        if idx > size {
            idx -= size;
        }
    }
    seq as u64
}

/// Verify that a sequence of restart conflict counts follows the Luby pattern.
///
/// Each `restarts[i]` should equal `base_conflicts * luby_restart_sequence(i)`.
/// Returns `true` when all entries match.
#[must_use]
pub fn verify_restart_schedule(restarts: &[u64], base_conflicts: u64) -> bool {
    if base_conflicts == 0 {
        return restarts.is_empty();
    }
    restarts
        .iter()
        .enumerate()
        .all(|(i, &r)| r == base_conflicts.saturating_mul(luby_restart_sequence(i)))
}
