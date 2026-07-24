// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! First UIP conflict analysis for CDCL solvers.
//!
//! When BCP detects a conflict (all literals in some clause are false),
//! conflict analysis walks the implication graph backwards from the conflict
//! clause to derive a learned clause. The standard algorithm stops at the
//! **first Unique Implication Point (UIP)**: the point where exactly one
//! literal from the current decision level remains in the resolvent.
//!
//! Reference: Handbook of Satisfiability (2nd ed.), Chapter 4, Section 4.4.

use super::{negate, var_of, CdclError, CdclState, Clause, Literal};

/// Result of conflict analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConflictAnalysisResult {
    /// The learned clause (first UIP cut).
    pub learned_clause: Clause,
    /// Backtrack level (second-highest decision level in learned clause).
    pub backtrack_level: u32,
    /// The first UIP literal (negation is the asserting literal).
    pub uip_literal: Literal,
}

/// Perform first-UIP conflict analysis.
///
/// Starting from the conflicting clause, resolve backwards along the
/// implication graph until exactly one literal from the current decision
/// level remains (the first UIP). The resolvent is the learned clause.
///
/// ## Algorithm (Handbook of Satisfiability, Ch. 4):
/// 1. Start with conflicting clause
/// 2. While more than one literal from current decision level in clause:
///    a. Pick the last-assigned literal from current level
///    b. Resolve with its reason clause
/// 3. The remaining literal from current level is the first UIP
/// 4. Backtrack level = max of non-UIP literal levels
#[must_use = "conflict analysis result contains the learned clause"]
pub fn analyze_conflict(
    state: &CdclState,
    conflict_clause_idx: usize,
) -> Result<ConflictAnalysisResult, CdclError> {
    if conflict_clause_idx >= state.clauses.len() {
        return Err(CdclError::ClauseIndexOutOfBounds {
            index: conflict_clause_idx,
            total: state.clauses.len(),
        });
    }

    let current_level = state.decision_level;
    let mut resolvent: Clause = state.clauses[conflict_clause_idx].clone();

    // Safety bound: resolve at most once per trail entry to prevent infinite loops.
    let max_iterations = state.trail.len();
    let mut iterations = 0;

    while count_at_level(state, &resolvent, current_level) > 1 {
        iterations += 1;
        if iterations > max_iterations {
            return Err(CdclError::UipNotFound);
        }

        let pivot_lit = last_assigned_at_level(state, &resolvent, current_level)
            .ok_or(CdclError::UipNotFound)?;
        let pivot_var = var_of(pivot_lit);

        // Find the reason clause for this literal.
        let reason_idx = find_reason(state, pivot_lit)?;
        let reason_clause = &state.clauses[reason_idx];

        resolvent = resolve(&resolvent, reason_clause, pivot_var)?;
    }

    // Identify the UIP literal: the single literal at current level.
    let uip_literal = resolvent
        .iter()
        .find(|&&lit| state.level_of(var_of(lit)).unwrap_or(0) == current_level)
        .copied()
        .ok_or(CdclError::UipNotFound)?;

    // Compute backtrack level: highest decision level among non-UIP literals.
    // If no other literals exist, backtrack to level 0.
    let backtrack_level = resolvent
        .iter()
        .filter(|&&lit| lit != uip_literal)
        .filter_map(|&lit| state.level_of(var_of(lit)))
        .max()
        .unwrap_or(0);

    Ok(ConflictAnalysisResult {
        learned_clause: resolvent,
        backtrack_level,
        uip_literal,
    })
}

/// Count how many literals in the clause are from the given decision level.
#[must_use]
fn count_at_level(state: &CdclState, clause: &[Literal], level: u32) -> usize {
    clause
        .iter()
        .filter(|&&lit| state.level_of(var_of(lit)).unwrap_or(0) == level)
        .count()
}

/// Find the last-assigned literal at the given decision level in the clause.
/// "Last assigned" means highest trail index.
#[must_use]
fn last_assigned_at_level(state: &CdclState, clause: &[Literal], level: u32) -> Option<Literal> {
    clause
        .iter()
        .filter(|&&lit| state.level_of(var_of(lit)).unwrap_or(0) == level)
        .max_by_key(|&&lit| state.trail_index_of(var_of(lit)).unwrap_or(0))
        .copied()
}

/// Find the reason clause index for a propagated literal on the trail.
fn find_reason(state: &CdclState, lit: Literal) -> Result<usize, CdclError> {
    let var = var_of(lit);
    for entry in &state.trail {
        if var_of(entry.literal) == var {
            return entry
                .reason
                .ok_or(CdclError::NoReasonClause { literal: lit });
        }
    }
    Err(CdclError::NoReasonClause { literal: lit })
}

/// Resolve two clauses on the given pivot variable.
///
/// The result is `(clause1 union clause2) \ {+pivot, -pivot}`, with
/// duplicates removed (by variable -- if both clauses contain the same
/// literal, it appears once in the result).
#[must_use = "resolution produces a new clause"]
pub fn resolve(
    clause1: &[Literal],
    clause2: &[Literal],
    pivot_var: u32,
) -> Result<Clause, CdclError> {
    let has_pivot_c1 = clause1.iter().any(|&l| var_of(l) == pivot_var);
    let has_pivot_c2 = clause2.iter().any(|&l| var_of(l) == pivot_var);
    if !has_pivot_c1 || !has_pivot_c2 {
        return Err(CdclError::ResolutionFailed { pivot_var });
    }

    let mut result = Vec::with_capacity(clause1.len() + clause2.len());
    let mut seen_vars = Vec::new();

    for &lit in clause1.iter().chain(clause2.iter()) {
        let v = var_of(lit);
        if v == pivot_var {
            continue;
        }
        if !seen_vars.contains(&v) {
            seen_vars.push(v);
            result.push(lit);
        }
    }

    Ok(result)
}

/// Verify that a learned clause is an asserting clause:
/// exactly one literal from the current decision level.
#[must_use]
pub fn is_asserting(state: &CdclState, clause: &[Literal]) -> bool {
    count_at_level(state, clause, state.decision_level) == 1
}

/// Bump VSIDS scores for all variables that participated in the conflict
/// analysis resolution chain. This is the standard "bump all resolved
/// variables" strategy from MiniSat.
///
/// Returns the list of variables whose scores were bumped.
#[must_use]
pub fn collect_conflict_variables(state: &CdclState, conflict_clause_idx: usize) -> Vec<u32> {
    let mut bumped = Vec::new();
    if conflict_clause_idx >= state.clauses.len() {
        return bumped;
    }

    // Collect all variables from the conflict clause.
    for &lit in &state.clauses[conflict_clause_idx] {
        let v = var_of(lit);
        if !bumped.contains(&v) {
            bumped.push(v);
        }
    }

    // Walk backwards through reason clauses to collect all resolved variables.
    let current_level = state.decision_level;
    let mut work: Vec<Literal> = state.clauses[conflict_clause_idx]
        .iter()
        .filter(|&&lit| {
            state.level_of(var_of(lit)).unwrap_or(0) == current_level
                && state
                    .trail
                    .iter()
                    .any(|e| var_of(e.literal) == var_of(lit) && e.reason.is_some())
        })
        .copied()
        .collect();

    while let Some(lit) = work.pop() {
        let var = var_of(lit);
        if let Some(entry) = state.trail.iter().find(|e| var_of(e.literal) == var) {
            if let Some(reason_idx) = entry.reason {
                if reason_idx < state.clauses.len() {
                    for &rlit in &state.clauses[reason_idx] {
                        let rv = var_of(rlit);
                        if !bumped.contains(&rv) {
                            bumped.push(rv);
                            if state.level_of(rv).unwrap_or(0) == current_level
                                && state
                                    .trail
                                    .iter()
                                    .any(|e| var_of(e.literal) == rv && e.reason.is_some())
                            {
                                work.push(rlit);
                            }
                        }
                    }
                }
            }
        }
    }

    bumped
}
