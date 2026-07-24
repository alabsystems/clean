// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ring normalization tactics (`ring`, `ring_nf`)
//!
//! Normalizes expressions in commutative (semi)rings to a canonical polynomial form.
//! Proof building for multi-step ring axiom compositions is in `ring_proof`.

use super::equality::match_equality;
pub(crate) use super::ring_helpers::make_eq;
use super::ring_helpers::{ring_exprs_equal, ring_normalize};
use super::ring_proof::try_build_ring_axiom_proof;
use super::ring_proof_carry::{combine_side_proofs, ring_normalize_with_proof};
use super::{rfl, ProofState, TacticError, TacticResult};

/// Ring normalization tactic for commutative (semi)rings.
///
/// Normalizes expressions in a ring to a canonical form, allowing
/// equality to be checked by syntactic comparison. Uses Horner form
/// for polynomial representation.
///
/// # Algorithm
/// 1. Flatten nested additions and multiplications
/// 2. Distribute multiplication over addition
/// 3. Collect like terms (same variable powers)
/// 4. Sort terms lexicographically
/// 5. Simplify coefficients
///
/// # Supported operations
/// - Addition (+)
/// - Multiplication (*)
/// - Subtraction (-) (converted to + neg)
/// - Negation (-)
/// - Natural number powers (^)
///
/// # Example
/// ```text
/// -- Goal: (a + b) * (a + b) = a * a + 2 * a * b + b * b
/// ring
/// -- Goal closed (both sides normalize to same form)
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `GoalMismatch` if goal is not an equality
/// - `Other` if normalization fails to close the goal
///
/// REQUIRES: `state.goals` is non-empty and the current goal target is an
/// equality when callers expect success.
/// ENSURES: On Ok, the current goal is closed via `rfl` after both sides
/// normalize to structurally equal `RingExpr`s.
/// ENSURES: On Err(GoalMismatch), the current goal target is not an equality.
/// ENSURES: On Err(ArithmeticFailed), the normalized sides differ and the proof
/// state is unchanged.
pub fn ring(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Check that goal is an equality
    let (_ty, lhs, rhs, _levels) = match_equality(&goal.target)
        .map_err(|_| TacticError::GoalMismatch("ring: goal is not an equality".to_string()))?;

    // Normalize both sides
    let lhs_norm = ring_normalize(&lhs);
    let rhs_norm = ring_normalize(&rhs);

    // Check if they're equal
    if ring_exprs_equal(&lhs_norm, &rhs_norm) {
        // Fast path: try rfl (works when normalized forms are definitionally equal)
        if rfl(state).is_ok() {
            return Ok(());
        }
        // Fall through to ring_nf for kernel proof output (#3368).
        // ring_nf builds explicit proof terms using ring axioms.
        return ring_nf(state);
    }

    Err(TacticError::ArithmeticFailed {
        tactic: "ring".to_string(),
        reason: format!("normalized forms differ:\n  LHS: {lhs_norm:?}\n  RHS: {rhs_norm:?}"),
    })
}

/// Normalize ring expressions to canonical form and close the goal.
///
/// Uses a three-tier proof strategy (#2501):
/// 1. Fast path: bounded post-hoc proof search for shallow axiom compositions
/// 2. Proof-carry normalizer: builds proofs during normalization for deeper cases
/// 3. ArithmeticFailed: unsupported heads or failed proof construction
///
/// No trustedArith fallback. Unsupported cases fail explicitly.
///
/// REQUIRES: `state.goals` is non-empty and the current goal target is an equality.
/// ENSURES: On Ok, the current goal is closed via a kernel-checkable proof.
/// ENSURES: On Err(GoalMismatch), the proof state is unchanged.
/// ENSURES: On Err(ArithmeticFailed), proof construction failed without trustedArith.
pub fn ring_nf(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let (_ty, lhs, rhs, _levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("ring_nf: goal must be an equality".to_string()))?;

    let lhs_norm = ring_normalize(&lhs);
    let rhs_norm = ring_normalize(&rhs);

    if ring_exprs_equal(&lhs_norm, &rhs_norm) {
        // Tier 1: fast post-hoc search (cheap, handles shallow cases)
        if let Some(proof) = try_build_ring_axiom_proof(state, &goal, &lhs, &rhs) {
            if state.close_goal(&goal, proof).is_ok() {
                return Ok(());
            }
        }
        // Tier 2: proof-carry normalizer (handles deeper reorderings)
        if let (Some(lhs_r), Some(rhs_r)) = (
            ring_normalize_with_proof(state, &goal, &lhs),
            ring_normalize_with_proof(state, &goal, &rhs),
        ) {
            if let Some(proof) = combine_side_proofs(state, &goal, &lhs_r, &rhs_r) {
                if state.close_goal(&goal, proof).is_ok() {
                    return Ok(());
                }
            }
        }
    }

    Err(TacticError::ArithmeticFailed {
        tactic: "ring_nf".to_string(),
        reason: format!(
            "proof construction failed without trustedArith\n  LHS norm: {lhs_norm:?}\n  RHS norm: {rhs_norm:?}"
        ),
    })
}
