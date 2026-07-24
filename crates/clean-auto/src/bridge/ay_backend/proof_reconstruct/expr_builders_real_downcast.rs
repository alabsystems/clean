// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real → Int downcast helpers for LRA additive path closing (#302).
//!
//! Converts Real-sort hypotheses to Int-sort via kernel axioms:
//! - `Real.ofNat_eq_ofInt`: normalizes `Real.ofNat(n)` to `Real.ofInt(Int.ofNat(n))`
//! - `Real.ofInt_add`: recursively normalizes `Real.add` trees into
//!   `Real.ofInt(Int.add(...))` (#2599)
//! - `Real.ofInt_le_to_Int`: converts `Real.ofInt(a) ≤ Real.ofInt(b)` to `Int.le a b`
//! - `Real.ofInt_lt_to_Int`: converts `Real.ofInt(a) < Real.ofInt(b)` to `Int.lt a b`

use super::expr_builders_arith::{
    combine_ops, extract_concrete_int_from_expr, mk_chain_step_for_sort, mk_int_concrete_false,
    CmpOp,
};
use super::real_downcast_normalize::normalize_real_cmp_proof_to_ofint;
use super::theory_lemma_lra::ActiveBound;
use super::theory_lemma_lra_additive::{
    mk_int_add, mk_int_add_cmp_add_left, mk_int_add_cmp_add_right,
};
use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// Extract the Int-level sub-expression from a Real endpoint expression.
///
/// Recognizes:
/// - `Real.ofInt(x)` → `Some(x)` (negative or any integer form)
/// - `Real.ofNat(n)` → `Some(Int.ofNat(n))` (non-negative, wrapped to Int)
///
/// Returns `None` for symbolic or unrecognized Real expressions.
pub(crate) fn extract_int_from_real_endpoint(expr: &Expr) -> Option<Expr> {
    let expr = expr.strip_mdata();
    if let ExprKind::App(f, arg) = expr.kind() {
        let f = f.strip_mdata();
        if let ExprKind::Const(name, _) = f.kind() {
            let s = name.to_string();
            if s == "Real.ofInt" {
                return Some((**arg).clone());
            }
            if s == "Real.ofNat" {
                return Some(Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    (**arg).clone(),
                ));
            }
        }
    }
    None
}

/// Extract a concrete integer value from a Real-sort kernel Expr pattern.
///
/// Recognizes:
/// - `Real.ofNat(NatLit(n))` → `n` (non-negative)
/// - `Real.ofInt(Int.ofNat(NatLit(n)))` → `n`
/// - `Real.ofInt(Int.negSucc(NatLit(n)))` → `-(n+1)` (negative)
///
/// Returns `None` for symbolic or unrecognized expressions.
pub(crate) fn extract_concrete_int_from_real_expr(expr: &Expr) -> Option<num_bigint::BigInt> {
    use super::theory_lemma_lra_sum_nf::eval_nat_to_bigint;
    let expr = expr.strip_mdata();
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
            let s = name.to_string();
            if s == "Real.ofNat" {
                return eval_nat_to_bigint(arg);
            }
            if s == "Real.ofInt" {
                return extract_concrete_int_from_expr(arg);
            }
        }
    }
    None
}

/// Build `@Real.ofInt_le_to_Int a b h : Int.le a b`.
pub(crate) fn mk_real_ofint_le_to_int(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Real.ofInt_le_to_Int"), vec![]),
                a.clone(),
            ),
            b.clone(),
        ),
        h.clone(),
    )
}

/// Build `@Real.ofInt_lt_to_Int a b h : Int.lt a b`.
pub(crate) fn mk_real_ofint_lt_to_int(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Real.ofInt_lt_to_Int"), vec![]),
                a.clone(),
            ),
            b.clone(),
        ),
        h.clone(),
    )
}

/// Build the downcast conversion for a Real hypothesis to Int level.
///
/// Recursively normalizes `Real.ofNat`, `Real.ofInt`, and nested additive
/// endpoint trees to `Real.ofInt`, then applies the
/// `Real.ofInt_{le,lt}_to_Int` conversion.
///
/// Returns `(a_int, b_int, h_int)` where `h_int : Int.{le,lt} a_int b_int`.
pub(crate) fn downcast_real_hyp_to_int(
    op: CmpOp,
    lhs_expr: &Expr,
    rhs_expr: &Expr,
    h_real: &Expr,
) -> Option<(Expr, Expr, Expr)> {
    let (lhs_norm, rhs_norm, current_h) =
        normalize_real_cmp_proof_to_ofint(op, lhs_expr, rhs_expr, h_real)?;
    let a_int = extract_int_from_real_endpoint(&lhs_norm)?;
    let b_int = extract_int_from_real_endpoint(&rhs_norm)?;

    let h_int = match op {
        CmpOp::Le => mk_real_ofint_le_to_int(&a_int, &b_int, &current_h),
        CmpOp::Lt => mk_real_ofint_lt_to_int(&a_int, &b_int, &current_h),
    };

    Some((a_int, b_int, h_int))
}

/// Real bound converted to the Int proof layer.
#[derive(Clone)]
pub(crate) struct DowncastedIntBound {
    pub(crate) lhs: Expr,
    pub(crate) rhs: Expr,
    pub(crate) proof: Expr,
    pub(crate) op: CmpOp,
}

/// Downcast an active Real bound to an Int comparison proof for weighted replay.
pub(crate) fn downcast_real_active_bound_to_int(
    bound: ActiveBound<'_>,
    clause_len: usize,
) -> Option<DowncastedIntBound> {
    let h_real = bound.hypothesis(clause_len);
    let (lhs, rhs, proof) =
        downcast_real_hyp_to_int(bound.op(), bound.lhs_expr(), bound.rhs_expr(), &h_real)?;
    Some(DowncastedIntBound {
        lhs,
        rhs,
        proof,
        op: bound.op(),
    })
}

/// Close the Real additive path by downcasting to Int level.
///
/// Converts each Real-level hypothesis (bound) to an Int-level hypothesis
/// via `Real.ofInt_{le,lt}_to_Int` after recursively normalizing its endpoint
/// tree to `Real.ofInt`, then builds an Int-level additive chain using
/// `Int.add_{le,lt}_add_{left,right}`, and closes with `mk_int_concrete_false`.
pub(crate) fn close_real_additive_via_int_downcast(
    bounds: &[ActiveBound<'_>],
    combined_op: CmpOp,
    clause_len: usize,
) -> Option<Expr> {
    let n = bounds.len();
    let mut int_lhs: Vec<Expr> = Vec::with_capacity(n);
    let mut int_rhs: Vec<Expr> = Vec::with_capacity(n);
    let mut int_hyps: Vec<Expr> = Vec::with_capacity(n);

    for bound in bounds.iter() {
        let h_real = bound.hypothesis(clause_len);
        let (a_int, b_int, h_int) =
            downcast_real_hyp_to_int(bound.op(), bound.lhs_expr(), bound.rhs_expr(), &h_real)?;
        int_lhs.push(a_int);
        int_rhs.push(b_int);
        int_hyps.push(h_int);
    }

    let (a_int, b_int) = (&int_lhs[0], &int_rhs[0]);
    let (c_int, d_int) = (&int_lhs[1], &int_rhs[1]);

    let step1 = mk_int_add_cmp_add_left(bounds[0].op(), a_int, b_int, &int_hyps[0], c_int);
    let step2 = mk_int_add_cmp_add_left(bounds[1].op(), c_int, d_int, &int_hyps[1], b_int);

    let mut acc_lhs = mk_int_add(c_int, a_int);
    let mut acc_rhs = mk_int_add(b_int, d_int);
    let sum_mid = mk_int_add(c_int, b_int);
    let mut acc_op = combine_ops(bounds[0].op(), bounds[1].op());

    let mut acc_proof = mk_chain_step_for_sort(
        &Sort::Int,
        &acc_lhs,
        &sum_mid,
        &acc_rhs,
        bounds[0].op(),
        bounds[1].op(),
        &step1,
        &step2,
    )?;

    for (i, bound) in bounds.iter().enumerate().skip(2) {
        let (ai, bi) = (&int_lhs[i], &int_rhs[i]);

        let step_a = mk_int_add_cmp_add_right(acc_op, &acc_lhs, &acc_rhs, &acc_proof, ai);
        let step_b = mk_int_add_cmp_add_left(bound.op(), ai, bi, &int_hyps[i], &acc_rhs);

        let new_lhs = mk_int_add(&acc_lhs, ai);
        let mid = mk_int_add(&acc_rhs, ai);
        let new_rhs = mk_int_add(&acc_rhs, bi);

        acc_proof = mk_chain_step_for_sort(
            &Sort::Int,
            &new_lhs,
            &mid,
            &new_rhs,
            acc_op,
            bound.op(),
            &step_a,
            &step_b,
        )?;
        acc_op = combine_ops(acc_op, bound.op());
        acc_lhs = new_lhs;
        acc_rhs = new_rhs;
    }

    let false_proof = mk_int_concrete_false(combined_op, &acc_lhs, &acc_rhs, &acc_proof);
    Some(false_proof)
}
