// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int/Real denominator-clearing bridge for constant-rational coefficients.

use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::super::super::core::{Goal, ProofState};
use super::super::super::equality::match_equality;
use super::super::linear_combination::LinearCoeff;
use super::expr_builders::{carrier_name, make_coeff_expr, make_eq_type, make_mul_app};
use super::{build_proof_with_negative_mode, try_close_with_proof, NegativeCoeffMode};

struct DenominatorPlan {
    scale: u64,
    scaled_coeffs: Vec<LinearCoeff>,
}

impl DenominatorPlan {
    fn build(alpha: &Expr, coeffs: &[LinearCoeff]) -> Option<Self> {
        match carrier_name(alpha)? {
            "Nat" | "Int" | "Real" => {}
            _ => return None,
        }
        let active_coeffs: Vec<_> = coeffs.iter().filter(|coeff| coeff.coeff.0 != 0).collect();
        if !active_coeffs.iter().any(|coeff| coeff.coeff.1 != 1) {
            return None;
        }

        let scale = active_coeffs
            .iter()
            .map(|coeff| coeff.coeff.1)
            .try_fold(1u64, checked_lcm_u64)?;
        if scale <= 1 {
            return None;
        }

        let scaled_coeffs = active_coeffs
            .iter()
            .map(|coeff| {
                let (num, den) = coeff.coeff;
                let factor = scale.checked_div(den)?;
                let scaled_num =
                    i64::try_from(i128::from(num).checked_mul(i128::from(factor))?).ok()?;
                Some(LinearCoeff::new(coeff.hyp_name.as_str(), scaled_num, 1))
            })
            .collect::<Option<Vec<_>>>()?;

        Some(Self {
            scale,
            scaled_coeffs,
        })
    }
}

pub(super) fn try_with_denominator_bridge(
    state: &ProofState,
    goal: &Goal,
    coeffs: &[LinearCoeff],
    negative_mode: NegativeCoeffMode,
) -> Option<Expr> {
    let target = state.metas.instantiate(&goal.target);
    let (alpha, goal_lhs, goal_rhs, levels) = match_equality(&target).ok()?;
    let eq_level = levels.first()?.clone();
    let plan = DenominatorPlan::build(&alpha, coeffs)?;
    let scale_expr = make_scale_expr(&alpha, plan.scale)?;

    let scaled_goal_lhs = make_mul_app(&alpha, &scale_expr, &goal_lhs)?;
    let scaled_goal_rhs = make_mul_app(&alpha, &scale_expr, &goal_rhs)?;
    let scaled_goal_ty = make_eq_type(&alpha, &scaled_goal_lhs, &scaled_goal_rhs, &eq_level);

    let scratch = state.clone_with_fresh_goal_target_in_context(scaled_goal_ty, &goal.local_ctx);
    let scratch_goal = scratch.current_goal()?.clone();
    let scaled_proof = build_proof_with_negative_mode(
        &scratch,
        &scratch_goal,
        &plan.scaled_coeffs,
        negative_mode,
    )?;

    let proof = apply_denominator_cancellation(
        state,
        &alpha,
        plan.scale,
        goal_lhs,
        goal_rhs,
        scaled_proof,
    )?;
    if try_close_with_proof(state, goal, &proof).is_ok() {
        Some(proof)
    } else {
        None
    }
}

fn make_scale_expr(alpha: &Expr, scale: u64) -> Option<Expr> {
    if scale == 0 {
        return None;
    }
    match carrier_name(alpha)? {
        "Nat" => Some(Expr::nat_lit(scale)),
        "Int" => Some(Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(scale),
        )),
        "Real" => make_coeff_expr(alpha, i64::try_from(scale).ok()?, 1),
        _ => None,
    }
}

fn apply_denominator_cancellation(
    state: &ProofState,
    alpha: &Expr,
    scale: u64,
    goal_lhs: Expr,
    goal_rhs: Expr,
    scaled_proof: Expr,
) -> Option<Expr> {
    let pred = Expr::nat_lit(scale.checked_sub(1)?);
    match carrier_name(alpha)? {
        "Nat" => {
            let theorem = Name::from_string("Nat.mul_left_cancel_succ");
            state.env().get_const(&theorem)?;
            Some(Expr::apps(
                Expr::const_(theorem, vec![]),
                [pred, goal_lhs, goal_rhs, scaled_proof],
            ))
        }
        "Int" => {
            let theorem = Name::from_string("Int.mul_left_cancel_ofNat_succ");
            state.env().get_const(&theorem)?;
            Some(Expr::apps(
                Expr::const_(theorem, vec![]),
                [pred, goal_lhs, goal_rhs, scaled_proof],
            ))
        }
        "Real" => {
            let theorem = Name::from_string("Real.mul_left_cancel_ofNat_succ");
            state.env().get_const(&theorem)?;
            Some(Expr::apps(
                Expr::const_(theorem, vec![]),
                [pred, goal_lhs, goal_rhs, scaled_proof],
            ))
        }
        _ => None,
    }
}

fn checked_lcm_u64(lhs: u64, rhs: u64) -> Option<u64> {
    if lhs == 0 || rhs == 0 {
        return None;
    }
    lhs.checked_div(gcd_u64(lhs, rhs))?.checked_mul(rhs)
}

fn gcd_u64(mut lhs: u64, mut rhs: u64) -> u64 {
    while rhs != 0 {
        let next = lhs % rhs;
        lhs = rhs;
        rhs = next;
    }
    lhs
}
