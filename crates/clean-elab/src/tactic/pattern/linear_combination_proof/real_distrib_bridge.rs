// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded Real distributivity replay for scratch normalization.

use clean_kernel::name::Name;
use clean_kernel::tc::whnf_proof::EqProofBuilder;
use clean_kernel::{Expr, ExprKind, Level};

use super::super::super::core::{Goal, ProofState};
use super::super::super::equality::match_equality;
use super::{make_add_app, make_mul_app};

pub(super) fn try_with_real_distrib_proof(
    state: &ProofState,
    goal: &Goal,
    eq_target: &Expr,
) -> Option<Expr> {
    let (alpha, lhs, rhs, levels) = match_equality(eq_target).ok()?;
    if super::expr_builders::carrier_name(&alpha)? != "Real" {
        return None;
    }
    let eq_level = levels.first()?.clone();

    try_build_real_distrib_eq(state, goal, &alpha, &eq_level, lhs.clone(), rhs.clone()).or_else(
        || {
            let proof = try_build_real_distrib_eq(
                state,
                goal,
                &alpha,
                &eq_level,
                rhs.clone(),
                lhs.clone(),
            )?;
            Some(EqProofBuilder::mk_eq_symm(eq_level, alpha, rhs, lhs, proof))
        },
    )
}

fn try_build_real_distrib_eq(
    state: &ProofState,
    goal: &Goal,
    alpha: &Expr,
    eq_level: &Level,
    lhs: Expr,
    rhs: Expr,
) -> Option<Expr> {
    let (coeff, add_lhs, add_rhs) = split_real_mul_add(&lhs)?;
    let direct_left = make_mul_app(alpha, &coeff, &add_lhs)?;
    let direct_right = make_mul_app(alpha, &coeff, &add_rhs)?;
    let direct_rhs = make_add_app(alpha, &direct_left, &direct_right)?;

    let distrib_theorem = Name::from_string("Real.distrib");
    state.env().get_const(&distrib_theorem)?;
    let distrib_proof = Expr::apps(
        Expr::const_(distrib_theorem, vec![]),
        [coeff.clone(), add_lhs.clone(), add_rhs.clone()],
    );

    if state.is_def_eq(goal, &rhs, &direct_rhs) {
        return Some(distrib_proof);
    }

    let commuted_rhs = make_add_app(alpha, &direct_right, &direct_left)?;
    if !state.is_def_eq(goal, &rhs, &commuted_rhs) {
        return None;
    }

    let add_comm = Name::from_string("Real.add_comm");
    state.env().get_const(&add_comm)?;
    let comm_proof = Expr::apps(
        Expr::const_(add_comm, vec![]),
        [direct_left.clone(), direct_right.clone()],
    );

    Some(EqProofBuilder::mk_eq_trans(
        eq_level.clone(),
        alpha.clone(),
        lhs,
        direct_rhs,
        commuted_rhs,
        distrib_proof,
        comm_proof,
    ))
}

fn split_real_mul_add(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let (coeff, sum_expr) = split_binary_const_app(expr, "Real.mul")?;
    let (lhs, rhs) = split_binary_const_app(&sum_expr, "Real.add")?;
    Some((coeff, lhs, rhs))
}

fn split_binary_const_app(expr: &Expr, op_name: &str) -> Option<(Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() != 2 {
        return None;
    }
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) if name.to_string() == op_name => {
            Some(((*args[0]).clone(), (*args[1]).clone()))
        }
        _ => None,
    }
}
