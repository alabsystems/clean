// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{mk_int_ofnat_expr, mk_var_expr, scale_bound, CmpOp, Sort};

fn int_add_height(expr: &super::Expr) -> usize {
    let super::ExprKind::App(fun, right) = expr.kind() else {
        return 0;
    };
    let super::ExprKind::App(head, left) = fun.kind() else {
        return 0;
    };
    let super::ExprKind::Const(name, _) = head.kind() else {
        return 0;
    };
    if name.to_string() != "Int.add" {
        return 0;
    }
    1 + int_add_height(left).max(int_add_height(right))
}

fn addition_leaf_count(expr: &super::Expr, add_name: &str, leaf: &super::Expr) -> Option<u64> {
    if expr == leaf {
        return Some(1);
    }
    let super::ExprKind::App(fun, right) = expr.kind() else {
        return None;
    };
    let super::ExprKind::App(head, left) = fun.kind() else {
        return None;
    };
    let super::ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != add_name {
        return None;
    }
    addition_leaf_count(left, add_name, leaf)?
        .checked_add(addition_leaf_count(right, add_name, leaf)?)
}

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
fn test_scale_bound_coefficient_5_uses_binary_addition_shape() {
    let lhs = mk_int_ofnat_expr(3);
    let rhs = mk_int_ofnat_expr(7);
    let hyp = mk_var_expr("h");

    let acc = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 5)
        .expect("coefficient 5 must produce a scaled accumulator");
    let lhs_double = super::mk_int_add(&lhs, &lhs);
    let lhs_quadruple = super::mk_int_add(&lhs_double, &lhs_double);
    let rhs_double = super::mk_int_add(&rhs, &rhs);
    let rhs_quadruple = super::mk_int_add(&rhs_double, &rhs_double);

    assert_eq!(acc.lhs, super::mk_int_add(&lhs_quadruple, &lhs));
    assert_eq!(acc.rhs, super::mk_int_add(&rhs_quadruple, &rhs));
    assert_eq!(acc.op, CmpOp::Le);
}

#[test]
fn test_scale_bound_coefficient_200_has_logarithmic_addition_depth() {
    let lhs = mk_int_ofnat_expr(3);
    let rhs = mk_int_ofnat_expr(7);
    let hyp = mk_var_expr("h");

    let acc = scale_bound(&Sort::Int, CmpOp::Le, &lhs, &rhs, &hyp, 200)
        .expect("coefficient 200 must produce a scaled accumulator");

    assert_eq!(int_add_height(&acc.lhs), 8);
    assert_eq!(int_add_height(&acc.rhs), 8);
}

#[test]
fn test_scale_bound_small_coefficient_semantic_matrix() {
    let lhs = mk_var_expr("lhs");
    let rhs = mk_var_expr("rhs");
    let hyp = mk_var_expr("hyp");

    for (sort, add_name) in [(Sort::Int, "Int.add"), (Sort::Real, "Real.add")] {
        for op in [CmpOp::Le, CmpOp::Lt] {
            for coeff in 1..=8 {
                let acc = scale_bound(&sort, op, &lhs, &rhs, &hyp, coeff)
                    .expect("positive Int/Real coefficients must scale");
                assert_eq!(
                    addition_leaf_count(&acc.lhs, add_name, &lhs),
                    Some(coeff),
                    "lhs copy count must equal the coefficient for {sort:?} {op:?} k={coeff}"
                );
                assert_eq!(
                    addition_leaf_count(&acc.rhs, add_name, &rhs),
                    Some(coeff),
                    "rhs copy count must equal the coefficient for {sort:?} {op:?} k={coeff}"
                );
                assert_eq!(
                    acc.op, op,
                    "positive scaling must preserve strictness for {sort:?} k={coeff}"
                );
            }
        }
    }
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
