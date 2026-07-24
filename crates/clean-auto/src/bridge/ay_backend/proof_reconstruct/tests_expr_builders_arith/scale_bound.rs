// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{mk_int_ofnat_expr, mk_var_expr, scale_bound, CmpOp, Sort};

#[test]
fn test_scale_bound_zero_coefficient_returns_none() {
    let lhs = mk_int_ofnat_expr(2);
    let rhs = mk_int_ofnat_expr(1);
    let hyp = mk_var_expr("h_two_le_one");

    assert!(
        scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 0).is_none(),
        "zero coefficient must not synthesize a vacuous scaled proof"
    );
}

#[test]
fn test_scale_bound_one_coefficient_returns_identity_accumulator() {
    let lhs = mk_int_ofnat_expr(2);
    let rhs = mk_int_ofnat_expr(1);
    let hyp = mk_var_expr("h_two_le_one");

    let scaled = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 1)
        .expect("coefficient 1 should return the original bound unchanged");

    assert_eq!(scaled.lhs, lhs);
    assert_eq!(scaled.rhs, rhs);
    assert_eq!(scaled.op, CmpOp::Le);
    assert_eq!(scaled.proof, hyp);
}

#[test]
fn test_scale_bound_moderate_coefficient_succeeds() {
    let lhs = mk_int_ofnat_expr(1);
    let rhs = mk_int_ofnat_expr(2);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 10);
    assert!(
        result.is_some(),
        "coefficient 10 must produce a valid scaled accumulator"
    );
    let acc = result.unwrap();
    assert_eq!(acc.op, CmpOp::Le, "all-Le chain must remain Le");
}

#[test]
fn test_scale_bound_coefficient_100_completes() {
    let lhs = mk_int_ofnat_expr(3);
    let rhs = mk_int_ofnat_expr(7);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 100);
    assert!(
        result.is_some(),
        "coefficient 100 must complete without OOM or stack overflow"
    );
}

#[test]
fn test_scale_bound_lt_coefficient_preserves_strictness() {
    let lhs = mk_int_ofnat_expr(1);
    let rhs = mk_int_ofnat_expr(2);
    let hyp = mk_var_expr("h");

    let result = scale_bound(&Sort::Int, CmpOp::Lt, &lhs, &rhs, &hyp, 5);
    assert!(result.is_some());
    let acc = result.unwrap();
    assert_eq!(
        acc.op,
        CmpOp::Lt,
        "scaling a Lt bound must preserve strictness"
    );
}
