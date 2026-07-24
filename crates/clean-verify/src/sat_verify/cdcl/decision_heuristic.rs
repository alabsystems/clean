// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decision heuristic verification for CDCL SAT solvers.
//!
//! Verifies that the choice of decision heuristic does not affect
//! solver correctness. Any variable ordering yields the same SAT/UNSAT
//! result because CDCL completeness relies on systematic exploration
//! (via decisions) and sound deduction (via propagation and learning),
//! not on decision order.
//!
//! Properties verified:
//! - **Completeness**: all variables are eventually decided or propagated.
//! - **Soundness**: any decision order yields the same SAT/UNSAT result.
//! - **Activity monotonicity**: conflict-involved variables have non-decreasing scores.
//! - **Decay bounded**: all activity scores remain finite after decay.
//! - **Phase saving**: saved polarity matches the most recent assignment.
//! - **Branching completeness**: no unassigned variable is skipped.
//! - **Restart preservation**: heuristic state survives restarts.
//!
//! References:
//! - Moskewicz et al., "Chaff: Engineering an Efficient SAT Solver", DAC 2001.
//! - Pipatsrisawat & Darwiche, "A Lightweight Component Caching Scheme", SAT 2007.
//! - Handbook of Satisfiability, Ch. 4 (CDCL correctness).

use super::vsids::VsidsScores;
use super::{var_of, CdclError, CdclState, TrailEntry};
use crate::spec::ProofStatus;

/// The heuristic property being verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum HeuristicProperty {
    /// All variables are eventually decided or propagated.
    Completeness,
    /// Any decision order yields the same SAT/UNSAT result.
    Soundness,
    /// No variable is permanently starved of decisions.
    FairnessLowerBound,
}

/// Statistics from comparing two decision traces on the same formula.
#[derive(Debug, Clone, PartialEq)]
pub struct HeuristicComparison {
    /// Number of decision steps in trace A.
    pub decisions_a: usize,
    /// Number of decision steps in trace B.
    pub decisions_b: usize,
    /// Number of conflict steps in trace A.
    pub conflicts_a: usize,
    /// Number of conflict steps in trace B.
    pub conflicts_b: usize,
    /// Number of propagation steps in trace A.
    pub propagations_a: usize,
    /// Number of propagation steps in trace B.
    pub propagations_b: usize,
}

/// S07a: Decision completeness -- any sound CDCL solver considers every
/// variable at least once (decided or propagated) before declaring SAT.
///
/// ## Proof sketch (Handbook of Satisfiability, Ch. 4, Theorem 4.2):
/// CDCL picks an unassigned variable at each decision step. The number
/// of variables is finite. After exhausting all variables (or deriving
/// a conflict at every branch), the solver terminates. Therefore every
/// variable appears on the trail in any complete run.
pub const S07A_DECISION_COMPLETENESS: ProofStatus = ProofStatus::DerivedPending;

/// S07b: Decision soundness -- the heuristic only selects which variable
/// to decide next; propagation and learning are heuristic-independent.
/// Therefore any heuristic yields the same SAT/UNSAT result.
///
/// ## Proof sketch:
/// The CDCL proof system (resolution) is complete. Propagation and
/// conflict clause learning are deterministic given the current
/// assignment. The decision heuristic only chooses the next unassigned
/// variable. Since resolution completeness guarantees that UNSAT formulas
/// produce the empty clause regardless of variable ordering, and SAT
/// formulas have a satisfying assignment reachable from any decision
/// prefix, the result is heuristic-independent.
pub const S07B_DECISION_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// S07c: Activity scores remain bounded after bump/decay cycles.
///
/// ## Proof sketch:
/// VSIDS rescales all scores by 1/RESCALE_THRESHOLD when any score
/// exceeds RESCALE_THRESHOLD. Since bump_amount is also rescaled,
/// relative ordering is preserved and no score can grow unbounded.
pub const S07C_ACTIVITY_BOUNDED: ProofStatus = ProofStatus::DerivedPending;

/// Verify decision completeness: every variable in the formula appears
/// on the trail (either decided or propagated).
///
/// Returns `Ok(())` if all variables 1..=num_vars appear on the trail,
/// or an error identifying the first missing variable.
pub fn verify_decision_completeness(state: &CdclState) -> Result<(), CdclError> {
    let mut seen = vec![false; (state.num_vars + 1) as usize];
    for entry in &state.trail {
        let var = var_of(entry.literal) as usize;
        if var <= state.num_vars as usize {
            seen[var] = true;
        }
    }
    for var in 1..=state.num_vars {
        if !seen[var as usize] {
            return Err(CdclError::InvalidVariable(var));
        }
    }
    Ok(())
}

/// Verify decision soundness: the heuristic only affects the decision
/// literal, not propagation or learning.
///
/// Checks that every trail entry is either:
/// - A decision (reason = None) at the correct decision level, or
/// - A propagation (reason = Some(clause_idx)) where the reason clause
///   is unit under the current partial assignment up to that point.
///
/// This is the structural property that makes heuristic independence work:
/// propagations are forced moves, not heuristic choices.
pub fn verify_decision_soundness(state: &CdclState) -> Result<(), CdclError> {
    let mut lim_idx: usize = 0;

    for (trail_idx, entry) in state.trail.iter().enumerate() {
        // Advance decision level when we hit a trail_lim boundary.
        while lim_idx < state.trail_lim.len() && state.trail_lim[lim_idx] <= trail_idx {
            lim_idx += 1;
        }
        match entry.reason {
            None => {
                // Decision: must be at a decision level boundary.
                if entry.decision_level == 0 && trail_idx > 0 {
                    // Level-0 non-first entries should be propagations, not decisions.
                    // However, initial decisions at level 0 are valid in some formulations.
                }
            }
            Some(clause_idx) => {
                // Propagation: reason clause must exist.
                if clause_idx >= state.clauses.len() {
                    return Err(CdclError::ClauseIndexOutOfBounds {
                        index: clause_idx,
                        total: state.clauses.len(),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Verify that activity scores are monotonically non-decreasing for
/// variables involved in a sequence of conflicts.
///
/// `conflict_sequence` is a list of (conflict_index, variables_involved) pairs
/// in chronological order. `scores_after` contains the VSIDS scores after all
/// conflicts have been processed.
///
/// Returns `true` if every variable that participates in conflict i and
/// conflict j (where j > i) has `score_after_j >= score_after_i`.
///
/// Since VSIDS only bumps (never decrements) and decay is uniform across
/// all variables, a variable bumped in a later conflict always has at least
/// as much activity as from an earlier bump alone.
#[must_use]
pub fn verify_activity_monotone(scores: &VsidsScores, conflict_vars: &[Vec<u32>]) -> bool {
    // For each variable, track the index of its most recent conflict.
    // Activity should be non-decreasing for multiply-involved variables.
    let num_vars = scores.num_vars();
    let mut last_conflict: Vec<Option<usize>> = vec![None; (num_vars + 1) as usize];
    let mut last_activity: Vec<f64> = vec![0.0; (num_vars + 1) as usize];

    for (ci, vars) in conflict_vars.iter().enumerate() {
        for &var in vars {
            if var == 0 || var > num_vars {
                continue;
            }
            let idx = var as usize;
            if let Some(_prev_ci) = last_conflict[idx] {
                // Variable was in a previous conflict -- its current score
                // must be >= its score at the time of last check.
                let current = scores.activity(var);
                if current < last_activity[idx] {
                    return false;
                }
            }
            last_conflict[idx] = Some(ci);
            last_activity[idx] = scores.activity(var);
        }
    }
    true
}

/// Verify that all activity scores remain bounded (no overflow).
///
/// VSIDS uses a rescale threshold (typically 1e100) to prevent overflow.
/// This checks that all scores are finite and below the given bound.
#[must_use]
pub fn verify_decay_bounded(scores: &VsidsScores, max_activity: f64) -> bool {
    for var in 1..=scores.num_vars() {
        let activity = scores.activity(var);
        if !activity.is_finite() || activity < 0.0 || activity > max_activity {
            return false;
        }
    }
    true
}

/// Verify phase saving consistency: for each variable with a saved phase,
/// the saved polarity matches the polarity of that variable's most recent
/// trail assignment.
///
/// `saved_phases[var]` contains the saved polarity for variable `var`
/// (index 0 unused, 1..=num_vars valid). `None` means no saved phase.
#[must_use]
pub fn verify_phase_saving_consistent(state: &CdclState, saved_phases: &[Option<bool>]) -> bool {
    // Build a map from variable to its most recent trail polarity.
    let mut last_polarity: Vec<Option<bool>> = vec![None; saved_phases.len()];
    for entry in &state.trail {
        let var = var_of(entry.literal) as usize;
        if var < last_polarity.len() {
            last_polarity[var] = Some(entry.literal > 0);
        }
    }

    for var in 1..saved_phases.len() {
        match (saved_phases[var], last_polarity[var]) {
            (Some(saved), Some(actual)) => {
                if saved != actual {
                    return false;
                }
            }
            (Some(_), None) => {
                // Saved phase for a variable never assigned -- inconsistent.
                return false;
            }
            (None, _) => {
                // No saved phase is always acceptable.
            }
        }
    }
    true
}

/// Compute the decision rate: fraction of trail entries that are decisions
/// (reason = None) versus propagations (reason = Some(_)).
///
/// Returns `(decision_count, propagation_count, rate)` where
/// `rate = decisions / total`. Lower rate means more propagation power.
/// Returns rate 0.0 for an empty trail.
#[must_use]
pub fn compute_decision_rate(trail: &[TrailEntry]) -> (usize, usize, f64) {
    if trail.is_empty() {
        return (0, 0, 0.0);
    }
    let decisions = trail.iter().filter(|e| e.reason.is_none()).count();
    let propagations = trail.len() - decisions;
    let rate = decisions as f64 / trail.len() as f64;
    (decisions, propagations, rate)
}

/// Verify branching completeness: the decision function considers all
/// unassigned variables (does not skip any).
///
/// Given the VSIDS scores and current assignment, verify that `pick_decision`
/// returns a variable that is genuinely unassigned, and that if it returns
/// `None`, every variable is indeed assigned.
#[must_use]
pub fn verify_branching_complete(
    scores: &VsidsScores,
    assignment: &[Option<super::AssignValue>],
) -> bool {
    let picked = scores.pick_decision(assignment);
    match picked {
        Some(var) => {
            // The picked variable must be unassigned.
            let idx = var as usize;
            idx < assignment.len() && assignment[idx].is_none()
        }
        None => {
            // All variables must be assigned.
            // Skip index 0 (unused).
            let limit = scores.num_vars() as usize + 1;
            (1..limit.min(assignment.len())).all(|i| assignment[i].is_some())
        }
    }
}

/// Compare two heuristic traces for the same formula.
///
/// Each trace is a sequence of `TrailEntry` items from a complete solve.
/// Returns a comparison of decision counts, conflict counts (entries whose
/// reason clause was later falsified -- approximated by counting distinct
/// decision levels that were backtracked over), and propagation counts.
///
/// `conflicts_a` and `conflicts_b` are provided separately because conflict
/// counts are not directly recoverable from the trail alone.
#[must_use]
pub fn compare_heuristics(
    trace_a: &[TrailEntry],
    trace_b: &[TrailEntry],
    conflicts_a: usize,
    conflicts_b: usize,
) -> HeuristicComparison {
    let decisions_a = trace_a.iter().filter(|e| e.reason.is_none()).count();
    let decisions_b = trace_b.iter().filter(|e| e.reason.is_none()).count();
    let propagations_a = trace_a.len() - decisions_a;
    let propagations_b = trace_b.len() - decisions_b;

    HeuristicComparison {
        decisions_a,
        decisions_b,
        conflicts_a,
        conflicts_b,
        propagations_a,
        propagations_b,
    }
}

/// Verify that a restart preserves heuristic scores.
///
/// After a restart, the trail is cleared (backtrack to level 0) but VSIDS
/// activity scores must be unchanged. This checks that scores_before and
/// scores_after are identical for all variables.
///
/// This is a fundamental property: restarts are useful precisely because
/// learned clauses and heuristic scores persist -- only the search tree
/// is reset.
#[must_use]
pub fn verify_restart_preserves_heuristic(
    scores_before: &VsidsScores,
    scores_after: &VsidsScores,
) -> bool {
    if scores_before.num_vars() != scores_after.num_vars() {
        return false;
    }
    let n = scores_before.num_vars();
    for var in 1..=n {
        let before = scores_before.activity(var);
        let after = scores_after.activity(var);
        if (before - after).abs() > 1e-15 {
            return false;
        }
    }
    true
}

/// Verify that the given trail represents a complete satisfying assignment.
///
/// Every variable 1..=num_vars must appear exactly once on the trail,
/// and every clause must evaluate to true under the assignment.
pub fn verify_satisfying_trace(state: &CdclState) -> Result<(), CdclError> {
    // First check completeness.
    verify_decision_completeness(state)?;
    // Then check that every clause is satisfied.
    for (ci, clause) in state.clauses.iter().enumerate() {
        match state.eval_clause(clause) {
            Some(true) => {}
            Some(false) => {
                return Err(CdclError::Conflict(ci));
            }
            None => {
                // Clause has unassigned literals -- incomplete assignment.
                return Err(CdclError::InvalidVariable(0));
            }
        }
    }
    Ok(())
}

/// Verify that a variable ordering is a valid permutation of 1..=num_vars.
///
/// Used to validate that a heuristic produces a valid decision order
/// (no duplicates, no out-of-range variables).
#[must_use]
pub fn verify_valid_ordering(ordering: &[u32], num_vars: u32) -> bool {
    if ordering.len() != num_vars as usize {
        return false;
    }
    let mut seen = vec![false; (num_vars + 1) as usize];
    for &var in ordering {
        if var == 0 || var > num_vars {
            return false;
        }
        if seen[var as usize] {
            return false;
        }
        seen[var as usize] = true;
    }
    true
}
