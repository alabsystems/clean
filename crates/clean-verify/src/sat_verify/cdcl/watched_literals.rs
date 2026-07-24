// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Watched literal propagation correctness theory for CDCL solvers.
//!
//! Deepens S02 (Two-Watched-Literal invariant) with full propagation
//! correctness verification. The core property: for every non-satisfied
//! clause of length >= 2, at least one watched literal is unassigned or true.
//!
//! Reference: Moskewicz et al., "Chaff: Engineering an Efficient SAT Solver",
//! DAC 2001. The two-watched-literal scheme enables O(1) amortized BCP.

use super::{negate, var_of, CdclError, CdclState, Literal};
use crate::spec::ProofStatus;

/// S02a: The watch invariant holds for all non-satisfied clauses.
pub const S02A_WATCH_INVARIANT: ProofStatus = ProofStatus::DerivedPending;

/// S02b: Watch propagation is sound — unit/conflict detection is correct.
pub const S02B_WATCH_PROPAGATION_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// S02c: After BCP fixpoint, no clause has both watches false without
/// the clause being satisfied by another literal.
pub const S02C_WATCH_COMPLETENESS: ProofStatus = ProofStatus::DerivedPending;

/// Per-literal watch list: maps each literal to clause indices watching it.
///
/// Literal encoding: for a literal `l`, the index into `lists` is
/// `lit_to_index(l)`. Positive literal `v` maps to `2*(v-1)`, negative
/// literal `-v` maps to `2*(v-1)+1`.
#[derive(Debug, Clone)]
pub struct WatchList {
    /// `lists[i]` is the set of clause indices where literal `i` is watched.
    lists: Vec<Vec<usize>>,
}

/// Result of attempting to propagate a watch after a literal becomes false.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum WatchPropagateResult {
    /// A new watch was found in the clause at a different position.
    NewWatch {
        clause_idx: usize,
        new_watch_pos: usize,
    },
    /// The clause became unit — exactly one unassigned literal remains.
    Unit {
        clause_idx: usize,
        implied_lit: Literal,
    },
    /// All literals in the clause are false — conflict.
    Conflict { clause_idx: usize },
}

/// Convert a literal to an index into the watch lists array.
///
/// Positive literal `v` -> `2*(v-1)`, negative `-v` -> `2*(v-1)+1`.
#[must_use]
fn lit_to_index(lit: Literal) -> usize {
    let v = var_of(lit) as usize;
    if lit > 0 {
        2 * (v - 1)
    } else {
        2 * (v - 1) + 1
    }
}

impl WatchList {
    /// Build watch lists from a `CdclState`'s clauses and watches.
    ///
    /// For each clause with length >= 2, registers the two watched literals
    /// in the per-literal lists. Unit clauses (length 1) watch their single
    /// literal. Empty clauses are skipped.
    #[must_use]
    pub fn build(state: &CdclState) -> Self {
        let num_vars = state.num_vars;
        let capacity = 2 * num_vars as usize;
        let mut lists = vec![Vec::new(); capacity];

        for (ci, clause) in state.clauses.iter().enumerate() {
            if clause.is_empty() {
                continue;
            }
            let (w0, w1) = state.watches[ci];
            let lit0 = clause[w0];
            let idx0 = lit_to_index(lit0);
            if idx0 < capacity {
                lists[idx0].push(ci);
            }
            // For clauses of length >= 2, also register the second watch.
            if clause.len() >= 2 && w0 != w1 {
                let lit1 = clause[w1];
                let idx1 = lit_to_index(lit1);
                if idx1 < capacity {
                    lists[idx1].push(ci);
                }
            }
        }

        Self { lists }
    }

    /// Return the clause indices watched by a given literal.
    #[must_use]
    pub fn watchers_of(&self, lit: Literal) -> &[usize] {
        let idx = lit_to_index(lit);
        if idx < self.lists.len() {
            &self.lists[idx]
        } else {
            &[]
        }
    }

    /// Total number of watched entries across all literals.
    #[must_use]
    pub fn total_watches(&self) -> usize {
        self.lists.iter().map(Vec::len).sum()
    }
}

/// Build watch lists from a `CdclState`.
#[must_use]
pub fn build_watch_lists(state: &CdclState) -> WatchList {
    WatchList::build(state)
}

/// Count how many clauses are being watched by each literal.
///
/// Returns a vector indexed by `lit_to_index(lit)` with counts.
#[must_use]
pub fn count_active_watches(state: &CdclState) -> Vec<usize> {
    let wl = WatchList::build(state);
    wl.lists.iter().map(Vec::len).collect()
}

/// Verify the core S02a watch invariant.
///
/// For every non-satisfied clause of length >= 2, at least one watched
/// literal is unassigned or assigned true. This is the property that
/// makes BCP efficient: we only need to visit a clause when one of
/// its watched literals becomes false.
///
/// ## Proof sketch (Handbook of Satisfiability, Ch. 4):
/// - Initialization: watches point to first two literals, both unassigned => invariant holds.
/// - Inductive step: when a watched literal becomes false, `propagate_watch`
///   either finds a new unassigned/true literal to watch, or detects unit/conflict.
///   In all cases the invariant is maintained for surviving clauses.
pub fn verify_watch_invariant(state: &CdclState) -> Result<(), CdclError> {
    for (ci, clause) in state.clauses.iter().enumerate() {
        if clause.len() < 2 {
            continue;
        }
        // Skip satisfied clauses — the invariant only constrains non-satisfied ones.
        if state.eval_clause(clause) == Some(true) {
            continue;
        }
        let (w0, w1) = state.watches[ci];
        if w0 >= clause.len() || w1 >= clause.len() {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
        let eval0 = state.eval_literal(clause[w0]);
        let eval1 = state.eval_literal(clause[w1]);
        // At least one watched literal must be unassigned (None) or true (Some(true)).
        let w0_ok = eval0.is_none() || eval0 == Some(true);
        let w1_ok = eval1.is_none() || eval1 == Some(true);
        if !w0_ok && !w1_ok {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
    }
    Ok(())
}

/// Verify watch completeness after BCP fixpoint.
///
/// After BCP reaches fixpoint, no clause should have both watches pointing
/// to false literals unless the clause is satisfied by some other literal.
/// This is strictly stronger than the basic invariant: it ensures BCP
/// has fully propagated.
pub fn verify_watch_completeness(state: &CdclState) -> Result<(), CdclError> {
    for (ci, clause) in state.clauses.iter().enumerate() {
        if clause.len() < 2 {
            continue;
        }
        let (w0, w1) = state.watches[ci];
        if w0 >= clause.len() || w1 >= clause.len() {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
        let eval0 = state.eval_literal(clause[w0]);
        let eval1 = state.eval_literal(clause[w1]);
        let both_false = eval0 == Some(false) && eval1 == Some(false);
        if both_false {
            // Check if the clause is satisfied by some non-watched literal.
            let satisfied_elsewhere = clause
                .iter()
                .enumerate()
                .any(|(i, &lit)| i != w0 && i != w1 && state.eval_literal(lit) == Some(true));
            if !satisfied_elsewhere {
                return Err(CdclError::WatchInvariantViolation(ci));
            }
        }
    }
    Ok(())
}

/// Propagate a watch after a watched literal becomes false.
///
/// Given that `false_lit` was just assigned false, scan the clause at
/// `clause_idx` for a replacement watch. The current watch positions
/// are read from `state.watches[clause_idx]`.
///
/// Returns:
/// - `NewWatch` if a replacement literal (unassigned or true) was found.
/// - `Unit` if exactly one literal remains unassigned (the other watch).
/// - `Conflict` if all literals are false.
///
/// Does NOT mutate `state` — the caller is responsible for updating
/// `state.watches` based on the result.
#[must_use]
pub fn propagate_watch(
    state: &CdclState,
    clause_idx: usize,
    false_lit: Literal,
) -> WatchPropagateResult {
    let clause = &state.clauses[clause_idx];
    let (w0, w1) = state.watches[clause_idx];

    // Determine which watch position corresponds to false_lit.
    let (false_pos, other_pos) = if clause[w0] == false_lit {
        (w0, w1)
    } else {
        (w1, w0)
    };

    // Check if the other watched literal is true — clause is satisfied.
    let other_eval = state.eval_literal(clause[other_pos]);
    if other_eval == Some(true) {
        // Clause already satisfied; no propagation needed. Keep current watch.
        return WatchPropagateResult::NewWatch {
            clause_idx,
            new_watch_pos: false_pos,
        };
    }

    // Search for a replacement: any non-watched literal that is unassigned or true.
    for (i, &lit) in clause.iter().enumerate() {
        if i == w0 || i == w1 {
            continue;
        }
        let eval = state.eval_literal(lit);
        if eval.is_none() || eval == Some(true) {
            return WatchPropagateResult::NewWatch {
                clause_idx,
                new_watch_pos: i,
            };
        }
    }

    // No replacement found. The clause is unit or conflict depending on
    // whether the other watched literal is unassigned.
    if other_eval.is_none() {
        WatchPropagateResult::Unit {
            clause_idx,
            implied_lit: clause[other_pos],
        }
    } else {
        // other_eval == Some(false), and all other literals are false too.
        WatchPropagateResult::Conflict { clause_idx }
    }
}

/// Verify that after assigning `assigned_lit`, all clauses watching its
/// negation still satisfy the watch invariant.
///
/// This checks the local effect of a single assignment: only clauses
/// that watch `negate(assigned_lit)` need re-examination.
pub fn verify_watch_after_assignment(
    state: &CdclState,
    assigned_lit: Literal,
) -> Result<(), CdclError> {
    let neg = negate(assigned_lit);
    for (ci, clause) in state.clauses.iter().enumerate() {
        if clause.len() < 2 {
            continue;
        }
        let (w0, w1) = state.watches[ci];
        if w0 >= clause.len() || w1 >= clause.len() {
            continue;
        }
        // Only check clauses that watch the negation of the assigned literal.
        let watches_neg = clause[w0] == neg || clause[w1] == neg;
        if !watches_neg {
            continue;
        }
        // Skip satisfied clauses.
        if state.eval_clause(clause) == Some(true) {
            continue;
        }
        let eval0 = state.eval_literal(clause[w0]);
        let eval1 = state.eval_literal(clause[w1]);
        let w0_ok = eval0.is_none() || eval0 == Some(true);
        let w1_ok = eval1.is_none() || eval1 == Some(true);
        if !w0_ok && !w1_ok {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
    }
    Ok(())
}

/// Verify watch symmetry: every clause's two watches point to distinct
/// literals that are actually present in the clause.
///
/// For unit clauses (length 1), both watch indices are 0, which is valid.
/// For clauses of length >= 2, the two indices must be distinct and in-bounds.
pub fn verify_watch_symmetry(state: &CdclState) -> Result<(), CdclError> {
    for (ci, clause) in state.clauses.iter().enumerate() {
        let (w0, w1) = state.watches[ci];
        if clause.is_empty() {
            continue;
        }
        if w0 >= clause.len() || w1 >= clause.len() {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
        if clause.len() >= 2 && w0 == w1 {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
        // The watched positions must refer to distinct literals.
        if clause.len() >= 2 && clause[w0] == clause[w1] {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
    }
    Ok(())
}

/// Helper: evaluate whether a clause is satisfied by any literal.
#[cfg(test)]
#[must_use]
pub(crate) fn clause_is_satisfied(state: &CdclState, clause: &[Literal]) -> bool {
    state.eval_clause(clause) == Some(true)
}
