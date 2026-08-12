// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boundary and resource tests for `scale_bound` and related additive
//! Farkas proof construction.
//!
//! Part of #2917 algorithm audit (iter 1514): verify off-by-one safety,
//! loop termination, and sort rejection at scale_bound boundaries.

use super::super::expr_builders_arith::CmpOp;
use super::super::theory_lemma_lra_additive::{mk_int_add, scale_bound};
use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::Expr;

fn mk_var_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_int_ofnat_expr(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::from_kind(clean_kernel::ExprKind::Lit(clean_kernel::Literal::Nat(
            clean_kernel::BigNat::Small(n),
        ))),
    )
}

#[test]
fn test_scale_bound_coefficient_1000_completes_within_resource_limits() {
    // Boundary test: coefficient 1000 exercises the uncapped binary addition
    // chain. In practice, ay Farkas coefficients after LCM rationalization are
    // almost always < 100, but larger inputs must remain logarithmic in depth.
    let lhs = mk_int_ofnat_expr(1);
    let rhs = mk_int_ofnat_expr(2);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 1000);
    assert!(
        result.is_some(),
        "coefficient 1000 must still produce a valid accumulator"
    );
    let acc = result.unwrap();
    assert_eq!(acc.op, CmpOp::Le, "all-Le scaling must remain Le at k=1000");
}

#[test]
fn test_scale_bound_coefficient_2_boundary() {
    // Boundary: coefficient 2 is the smallest value that enters the loop body.
    // Verify the k=2 base case builds correct structure.
    let lhs = mk_int_ofnat_expr(3);
    let rhs = mk_int_ofnat_expr(7);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 2);
    assert!(result.is_some());
    let acc = result.unwrap();

    // LHS should be Int.add(3, 3) = 2*3
    assert_eq!(acc.lhs, mk_int_add(&lhs, &lhs));
    // RHS should be Int.add(7, 7) = 2*7
    assert_eq!(acc.rhs, mk_int_add(&rhs, &rhs));
    assert_eq!(acc.op, CmpOp::Le);
}

#[test]
fn test_scale_bound_coefficient_3_extends_base() {
    // Boundary: coefficient 3 combines the unit and doubled accumulators.
    let lhs = mk_int_ofnat_expr(1);
    let rhs = mk_int_ofnat_expr(2);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 3);
    assert!(result.is_some());
    let acc = result.unwrap();

    // LHS = add(add(1, 1), 1) = 3*1
    let double_lhs = mk_int_add(&lhs, &lhs);
    assert_eq!(acc.lhs, mk_int_add(&double_lhs, &lhs));
    // RHS = add(add(2, 2), 2) = 3*2
    let double_rhs = mk_int_add(&rhs, &rhs);
    assert_eq!(acc.rhs, mk_int_add(&double_rhs, &rhs));
}

#[test]
fn test_scale_bound_lt_at_boundary_coefficient_2() {
    // Lt with k=2: the combined op should still be Lt (Lt + Lt = Lt).
    let lhs = mk_int_ofnat_expr(1);
    let rhs = mk_int_ofnat_expr(2);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Lt, &lhs, &rhs, &hyp, 2);
    assert!(result.is_some());
    assert_eq!(
        result.unwrap().op,
        CmpOp::Lt,
        "Lt + Lt at k=2 must remain Lt"
    );
}

#[test]
fn test_scale_bound_real_sort_works_at_boundary() {
    // Verify Real sort also works with the same boundary conditions.
    let lhs = mk_var_expr("a");
    let rhs = mk_var_expr("b");
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Real, CmpOp::Le, &lhs, &rhs, &hyp, 3);
    assert!(
        result.is_some(),
        "scale_bound with Real sort and k=3 must succeed"
    );
}

#[test]
fn test_scale_bound_unsupported_sort_returns_none() {
    // Bool sort is unsupported for arithmetic scaling.
    let lhs = mk_var_expr("a");
    let rhs = mk_var_expr("b");
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Bool, CmpOp::Le, &lhs, &rhs, &hyp, 2);
    assert!(
        result.is_none(),
        "scale_bound on Bool sort must return None"
    );
}
