// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear combination proof reconstruction.
//!
//! Builds kernel-valid equality proofs from weighted hypothesis combinations.
//! Shared between `linear_combination` and `polyrith` (#2526).
//!
//! The approach: given hypotheses `h_i : a_i = b_i` with coefficients `c_i`,
//! build a proof of `sum(c_i * a_i) = sum(c_i * b_i)` using congruence and
//! transitivity, then connect back to the original goal via scratch-state
//! normalization.

use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{Expr, ExprKind, Level};

use super::super::core::{Goal, ProofState};
use super::super::equality::match_equality;
use super::super::ring_nf;
use super::linear_combination::LinearCoeff;
use super::util::try_extract_eq;

mod cancellation_bridge;
mod denominator_bridge;
mod expr_builders;
mod real_distrib_bridge;

use cancellation_bridge::try_with_cancellation_bridge;
use denominator_bridge::try_with_denominator_bridge;
use expr_builders::{make_add_app, make_add_left_lambda, make_add_right_lambda};
use expr_builders::{make_coeff_expr, make_eq_type, make_mul_app, make_mul_lambda};
use real_distrib_bridge::try_with_real_distrib_proof;

/// Equality accumulator: tracks `(lhs, rhs, proof)` through combination steps.
///
/// Analogous to `NatLeAcc` in `arith_linarith_proof.rs` but for equalities.
struct EqAcc {
    alpha: Expr,
    u: Level,
    lhs: Expr,
    rhs: Expr,
    proof: Expr,
}

impl EqAcc {
    /// From a hypothesis `h : a = b` with coefficient 1.
    fn from_hypothesis(
        hyp_fvar: &Expr,
        hyp_ty: &Expr,
        state: &ProofState,
        goal: &Goal,
    ) -> Option<Self> {
        let (alpha, lhs, rhs) = extract_eq_components(hyp_ty)?;
        let u = get_sort_level(state, goal, &alpha)?;
        Some(EqAcc {
            alpha,
            u,
            lhs,
            rhs,
            proof: hyp_fvar.clone(),
        })
    }

    /// From a hypothesis `h : a = b` scaled by coefficient `num / den`.
    /// Builds: `congr_arg (fun x => c * x) h : c * a = c * b`
    fn from_scaled(
        hyp_fvar: &Expr,
        hyp_ty: &Expr,
        num: i64,
        den: u64,
        state: &ProofState,
        goal: &Goal,
    ) -> Option<Self> {
        let (alpha, a, b) = extract_eq_components(hyp_ty)?;
        let u = get_sort_level(state, goal, &alpha)?;
        let coeff_expr = make_coeff_expr(&alpha, num, den)?;
        let mul_fn = make_mul_lambda(&alpha, &coeff_expr)?;

        let proof = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: u.clone(),
            v: u.clone(),
            alpha: alpha.clone(),
            beta: alpha.clone(),
            f: mul_fn,
            a1: a.clone(),
            a2: b.clone(),
            h: hyp_fvar.clone(),
        });

        let lhs = make_mul_app(&alpha, &coeff_expr, &a)?;
        let rhs = make_mul_app(&alpha, &coeff_expr, &b)?;
        Some(EqAcc {
            alpha,
            u,
            lhs,
            rhs,
            proof,
        })
    }

    /// Combine: `self : a1 = b1` and `next : a2 = b2`
    /// → `(a1 + a2) = (b1 + b2)` via two-step congruence + transitivity.
    fn combine(self, next: EqAcc) -> Option<EqAcc> {
        // Step 1: congr_arg (fun x => x + next.lhs) self.proof
        let step1 = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: self.u.clone(),
            v: self.u.clone(),
            alpha: self.alpha.clone(),
            beta: self.alpha.clone(),
            f: make_add_left_lambda(&self.alpha, &next.lhs)?,
            a1: self.lhs.clone(),
            a2: self.rhs.clone(),
            h: self.proof,
        });

        // Step 2: congr_arg (fun y => self.rhs + y) next.proof
        let step2 = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: self.u.clone(),
            v: self.u.clone(),
            alpha: self.alpha.clone(),
            beta: self.alpha.clone(),
            f: make_add_right_lambda(&self.alpha, &self.rhs)?,
            a1: next.lhs.clone(),
            a2: next.rhs.clone(),
            h: next.proof,
        });

        let combined_lhs = make_add_app(&self.alpha, &self.lhs, &next.lhs)?;
        let middle = make_add_app(&self.alpha, &self.rhs, &next.lhs)?;
        let combined_rhs = make_add_app(&self.alpha, &self.rhs, &next.rhs)?;

        let proof = EqProofBuilder::mk_eq_trans(
            self.u.clone(),
            self.alpha.clone(),
            combined_lhs.clone(),
            middle,
            combined_rhs.clone(),
            step1,
            step2,
        );

        Some(EqAcc {
            alpha: self.alpha,
            u: self.u,
            lhs: combined_lhs,
            rhs: combined_rhs,
            proof,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NegativeCoeffMode {
    PreferCarrierScaling,
    PreferSymmetry,
}

/// Build a proof of the goal via linear combination of equality hypotheses.
///
/// Returns `None` when any step fails. Callers fall back to `trustedArith`.
///
/// REQUIRES: `state.goals` is non-empty with an equality goal
/// ENSURES: On Some(proof), `proof` is a kernel-valid proof of the goal target
/// ENSURES: On None, proof reconstruction was not possible
pub(crate) fn build_linear_combination_eq_proof(
    state: &ProofState,
    goal: &Goal,
    coeffs: &[LinearCoeff],
) -> Option<Expr> {
    if coeffs.is_empty() {
        return None;
    }

    if let Some(proof) =
        build_proof_with_negative_mode(state, goal, coeffs, NegativeCoeffMode::PreferCarrierScaling)
    {
        return Some(proof);
    }

    if coeffs.iter().any(|coeff| coeff.coeff.0 < 0) {
        return build_proof_with_negative_mode(
            state,
            goal,
            coeffs,
            NegativeCoeffMode::PreferSymmetry,
        );
    }

    None
}

fn build_proof_with_negative_mode(
    state: &ProofState,
    goal: &Goal,
    coeffs: &[LinearCoeff],
    negative_mode: NegativeCoeffMode,
) -> Option<Expr> {
    let Some(acc) = build_combined_equality(state, goal, coeffs, negative_mode) else {
        if has_fractional_coeff(coeffs) {
            return try_with_denominator_bridge(state, goal, coeffs, negative_mode);
        }
        return None;
    };
    // Try closing directly if the combined proof type matches the goal
    if try_close_with_proof(state, goal, &acc.proof).is_ok() {
        return Some(acc.proof);
    }

    // Fractional coefficients that built an accumulator are still on the
    // direct-close lane from #2573. Rat can continue into the cancellation
    // bridge (#2588); Nat/Int fractional replay was already handled by the
    // denominator bridge before reaching this point.
    if has_fractional_coeff(coeffs) && !supports_fractional_followon(&acc.alpha) {
        return None;
    }

    if let Some(proof) = try_with_cancellation_bridge(state, goal, &acc) {
        return Some(proof);
    }

    // Try scratch-state ring_nf normalization to connect combo ↔ goal
    if let Some(proof) = try_with_scratch_normalization(state, goal, &acc) {
        return Some(proof);
    }

    if has_fractional_coeff(coeffs) {
        return try_with_denominator_bridge(state, goal, coeffs, negative_mode);
    }

    None
}

/// Phase 1: Build the combined equality from hypothesis coefficients.
fn build_combined_equality(
    state: &ProofState,
    goal: &Goal,
    coeffs: &[LinearCoeff],
    negative_mode: NegativeCoeffMode,
) -> Option<EqAcc> {
    let mut acc: Option<EqAcc> = None;

    for coeff in coeffs {
        let (num, den) = coeff.coeff;
        if num == 0 {
            continue;
        }

        let hyp = goal.local_ctx.iter().find(|h| h.name == coeff.hyp_name)?;
        let hyp_ty = state.metas.instantiate(&hyp.ty);
        let hyp_fvar = Expr::fvar(hyp.fvar);

        let entry = build_coeff_entry(&hyp_fvar, &hyp_ty, num, den, state, goal, negative_mode)?;

        acc = match acc {
            None => Some(entry),
            Some(prev) => Some(prev.combine(entry)?),
        };
    }

    acc
}

/// Build a single accumulator entry for a hypothesis with the given coefficient.
fn build_coeff_entry(
    hyp_fvar: &Expr,
    hyp_ty: &Expr,
    num: i64,
    den: u64,
    state: &ProofState,
    goal: &Goal,
    negative_mode: NegativeCoeffMode,
) -> Option<EqAcc> {
    if num == 1 && den == 1 {
        EqAcc::from_hypothesis(hyp_fvar, hyp_ty, state, goal)
    } else if num > 0 {
        EqAcc::from_scaled(hyp_fvar, hyp_ty, num, den, state, goal)
    } else if negative_mode == NegativeCoeffMode::PreferCarrierScaling {
        EqAcc::from_scaled(hyp_fvar, hyp_ty, num, den, state, goal)
            .or_else(|| build_negative_symmetry_entry(hyp_fvar, hyp_ty, num, den, state, goal))
    } else {
        build_negative_symmetry_entry(hyp_fvar, hyp_ty, num, den, state, goal)
    }
}

fn build_negative_symmetry_entry(
    hyp_fvar: &Expr,
    hyp_ty: &Expr,
    num: i64,
    den: u64,
    state: &ProofState,
    goal: &Goal,
) -> Option<EqAcc> {
    if num == -1 && den == 1 {
        let (alpha, a, b) = extract_eq_components(hyp_ty)?;
        let u = get_sort_level(state, goal, &alpha)?;
        let symm_proof = EqProofBuilder::mk_eq_symm(
            u.clone(),
            alpha.clone(),
            a.clone(),
            b.clone(),
            hyp_fvar.clone(),
        );
        Some(EqAcc {
            alpha,
            u,
            lhs: b,
            rhs: a,
            proof: symm_proof,
        })
    } else if num < 0 {
        // Negative: symmetrize then scale by |num|
        let (alpha, a, b) = extract_eq_components(hyp_ty)?;
        let u = get_sort_level(state, goal, &alpha)?;
        let symm_proof = EqProofBuilder::mk_eq_symm(
            u.clone(),
            alpha.clone(),
            a.clone(),
            b.clone(),
            hyp_fvar.clone(),
        );
        let symm_ty = make_eq_type(&alpha, &b, &a, &u);
        EqAcc::from_scaled(&symm_proof, &symm_ty, num.checked_neg()?, den, state, goal)
    } else {
        None
    }
}

fn has_fractional_coeff(coeffs: &[LinearCoeff]) -> bool {
    coeffs
        .iter()
        .any(|coeff| coeff.coeff.0 != 0 && coeff.coeff.1 != 1)
}

/// Rat carrier supports post-direct-close recovery via cancellation bridge
/// (#2588). Nat/Int fractional coefficients use the denominator bridge before
/// an accumulator exists, so only Rat has a follow-on path here.
fn supports_fractional_followon(alpha: &Expr) -> bool {
    matches!(expr_builders::carrier_name(alpha), Some("Rat" | "Real"))
}

/// Check if the proof's type matches the goal target.
fn try_close_with_proof(state: &ProofState, goal: &Goal, proof: &Expr) -> Result<(), ()> {
    let proof_ty = state.infer_type(goal, proof).map_err(|_| ())?;
    let target = state.metas.instantiate(&goal.target);
    if state.is_def_eq(goal, &proof_ty, &target) {
        Ok(())
    } else {
        Err(())
    }
}

/// Connect the combined equality to the goal via scratch-state normalization.
fn try_with_scratch_normalization(state: &ProofState, goal: &Goal, acc: &EqAcc) -> Option<Expr> {
    let target = state.metas.instantiate(&goal.target);
    let (goal_lhs, goal_rhs) = try_extract_eq(&target)?;

    let left_proof = prove_eq_by_ring_nf(
        state,
        goal,
        make_eq_type(&acc.alpha, &goal_lhs, &acc.lhs, &acc.u),
    )?;
    let right_proof = prove_eq_by_ring_nf(
        state,
        goal,
        make_eq_type(&acc.alpha, &acc.rhs, &goal_rhs, &acc.u),
    )?;

    let inner = EqProofBuilder::mk_eq_trans(
        acc.u.clone(),
        acc.alpha.clone(),
        acc.lhs.clone(),
        acc.rhs.clone(),
        goal_rhs.clone(),
        acc.proof.clone(),
        right_proof,
    );

    Some(EqProofBuilder::mk_eq_trans(
        acc.u.clone(),
        acc.alpha.clone(),
        goal_lhs,
        acc.lhs.clone(),
        goal_rhs,
        left_proof,
        inner,
    ))
}

/// Prove an equality via `ring_nf` in a scratch proof state.
/// Returns `None` if normalization fails or records `trustedArith`.
fn prove_eq_by_ring_nf(state: &ProofState, goal: &Goal, eq_target: Expr) -> Option<Expr> {
    let eq_target_for_fallback = eq_target.clone();
    let mut scratch = state.clone_with_fresh_goal_target_in_context(eq_target, &goal.local_ctx);

    if ring_nf(&mut scratch).is_err() {
        return try_with_real_distrib_proof(state, goal, &eq_target_for_fallback);
    }
    if !scratch.is_complete() {
        return try_with_real_distrib_proof(state, goal, &eq_target_for_fallback);
    }
    if scratch.trust_ledger().trusted_arith_count > 0 {
        return try_with_real_distrib_proof(state, goal, &eq_target_for_fallback);
    }
    scratch
        .proof_term()
        .or_else(|| try_with_real_distrib_proof(state, goal, &eq_target_for_fallback))
}

fn extract_eq_components(ty: &Expr) -> Option<(Expr, Expr, Expr)> {
    let (alpha, a, b, _levels) = match_equality(ty).ok()?;
    Some((alpha, a, b))
}

fn get_sort_level(state: &ProofState, goal: &Goal, ty: &Expr) -> Option<Level> {
    let sort = state.infer_type(goal, ty).ok()?;
    match sort.kind() {
        ExprKind::Sort(level) => Some(level.clone()),
        _ => None,
    }
}
