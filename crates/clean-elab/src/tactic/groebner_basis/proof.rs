// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, Level};

use super::super::polynomial::VarMap;
use super::super::{match_equality, Goal, ProofState};
use super::basis::{
    buchberger_basis_with_combinations, compose_basis_quotients,
    reduce_rational_by_basis_with_quotients,
};
use super::preprocess::expr_to_int_polynomial;
use super::proof_exprs::{
    cancel_shared_additive_witness, make_add_app, make_eq_type, prove_eq_by_ring_nf,
    rational_polynomial_to_expr, try_close_with_proof,
};
use super::types::{EqAcc, EqualityHypothesis, GroebnerConfig, Rational, RationalPolynomial};
use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};

pub(crate) fn groebner_goal_proof(
    state: &ProofState,
    goal: &Goal,
    config: &GroebnerConfig,
) -> Option<Expr> {
    let target = state.metas.instantiate(&goal.target);
    let (alpha, goal_lhs, goal_rhs, _levels) = match_equality(&target).ok()?;

    let mut poly_var_map = VarMap::new();
    let mut generators = Vec::new();
    let mut hypotheses = Vec::new();

    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        let Ok((_hyp_ty, lhs, rhs, _levels)) = match_equality(&ty) else {
            continue;
        };
        let Some(lhs_poly) = expr_to_int_polynomial(&lhs, &mut poly_var_map) else {
            continue;
        };
        let Some(rhs_poly) = expr_to_int_polynomial(&rhs, &mut poly_var_map) else {
            continue;
        };
        generators.push(lhs_poly.sub(&rhs_poly));
        hypotheses.push(EqualityHypothesis {
            fvar: decl.fvar,
            lhs,
            rhs,
        });
    }

    if generators.is_empty() {
        return None;
    }

    let goal_poly = expr_to_int_polynomial(&goal_lhs, &mut poly_var_map)?
        .sub(&expr_to_int_polynomial(&goal_rhs, &mut poly_var_map)?);
    if goal_poly.is_zero() {
        return None;
    }

    let basis = buchberger_basis_with_combinations(&generators, config);
    let basis_polys: Vec<_> = basis.iter().map(|elt| elt.poly.clone()).collect();
    let goal_poly = RationalPolynomial::from_integer(&goal_poly);
    let (remainder, quotient_basis) =
        reduce_rational_by_basis_with_quotients(&goal_poly, &basis_polys);
    if !remainder.is_zero() {
        return None;
    }

    let combination = compose_basis_quotients(&quotient_basis, &basis, generators.len());
    build_goal_membership_proof(
        state,
        goal,
        &alpha,
        &goal_lhs,
        &goal_rhs,
        &hypotheses,
        &combination,
        &poly_var_map,
    )
}

fn build_goal_membership_proof(
    state: &ProofState,
    goal: &Goal,
    alpha: &Expr,
    goal_lhs: &Expr,
    goal_rhs: &Expr,
    hypotheses: &[EqualityHypothesis],
    combination: &[RationalPolynomial],
    poly_var_map: &VarMap,
) -> Option<Expr> {
    let acc = build_polynomial_combination_acc(
        state,
        goal,
        alpha,
        hypotheses,
        combination,
        poly_var_map,
    )?;
    if try_close_with_proof(state, goal, &acc.proof).is_ok() {
        return Some(acc.proof);
    }
    let u = acc.u.clone();
    let witness = acc.rhs.clone();
    let bridge_target = make_eq_type(
        alpha,
        &make_add_app(alpha, goal_lhs, &witness)?,
        &make_add_app(alpha, goal_rhs, &acc.lhs)?,
        &u,
    );
    let left_bridge = prove_eq_by_ring_nf(state, goal, bridge_target)?;
    let right_bridge = EqProofBuilder::mk_congr_arg(CongrArgArgs {
        u: u.clone(),
        v: u.clone(),
        alpha: alpha.clone(),
        beta: alpha.clone(),
        f: super::proof_exprs::make_add_right_lambda(alpha, goal_rhs)?,
        a1: acc.lhs.clone(),
        a2: witness.clone(),
        h: acc.proof,
    });
    let bridged_eq = EqProofBuilder::mk_eq_trans(
        u,
        alpha.clone(),
        make_add_app(alpha, goal_lhs, &witness)?,
        make_add_app(alpha, goal_rhs, &acc.lhs)?,
        make_add_app(alpha, goal_rhs, &witness)?,
        left_bridge,
        right_bridge,
    );

    cancel_shared_additive_witness(
        state,
        goal,
        alpha,
        goal_lhs.clone(),
        goal_rhs.clone(),
        witness,
        bridged_eq,
    )
}

fn build_polynomial_combination_acc(
    state: &ProofState,
    goal: &Goal,
    alpha: &Expr,
    hypotheses: &[EqualityHypothesis],
    combination: &[RationalPolynomial],
    poly_var_map: &VarMap,
) -> Option<EqAcc> {
    let u: Level = super::proof_exprs::get_sort_level(state, goal, alpha)?;
    let mut acc: Option<EqAcc> = None;

    for (hypothesis, coeff_poly) in hypotheses.iter().zip(combination) {
        if coeff_poly.is_zero() {
            continue;
        }

        let scaled = if coeff_poly.as_constant() == Some(Rational::one()) {
            EqAcc::from_hypothesis(
                alpha,
                &u,
                &Expr::fvar(hypothesis.fvar),
                &hypothesis.lhs,
                &hypothesis.rhs,
            )?
        } else {
            let coeff_expr = rational_polynomial_to_expr(coeff_poly, poly_var_map, alpha)?;
            EqAcc::from_scaled_expr(
                alpha,
                &u,
                &Expr::fvar(hypothesis.fvar),
                &hypothesis.lhs,
                &hypothesis.rhs,
                &coeff_expr,
            )?
        };
        acc = match acc {
            None => Some(scaled),
            Some(prev) => Some(prev.combine(scaled)?),
        };
    }

    acc
}
