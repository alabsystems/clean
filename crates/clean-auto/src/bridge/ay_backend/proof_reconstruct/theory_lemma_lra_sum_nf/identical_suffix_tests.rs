// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::super::theory_lemma_lra_additive::mk_int_add;
use super::{identical_suffix::try_close_identical_raw_add_suffix, mk_int_literal, CmpOp};

fn mk_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => expr_contains_const(f, target) || expr_contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, target)
                || expr_contains_const(val, target)
                || expr_contains_const(body, target)
        }
        _ => false,
    }
}

#[test]
fn test_identical_raw_add_suffix_fast_path_closes_concrete_residual() {
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_int_add(&mk_int_add(&mk_int_literal(4), &x), &y);
    let rhs = mk_int_add(&mk_int_add(&mk_int_literal(3), &x), &y);
    let proof = mk_var("h");

    let false_proof = try_close_identical_raw_add_suffix(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("identical raw right suffixes should use direct cancellation");

    assert!(
        expr_contains_const(&false_proof, "Int.le_of_add_le_add_right"),
        "fast path must derive the residual comparison through the kernel cancellation lemma"
    );
    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "fast path must close the concrete residual through the kernel contradiction builder"
    );
}

#[test]
fn test_identical_raw_add_suffix_fast_path_rejects_mismatched_suffix() {
    let lhs = mk_int_add(&mk_int_literal(4), &mk_var("x"));
    let rhs = mk_int_add(&mk_int_literal(3), &mk_var("y"));
    let proof = mk_var("h");

    assert!(
        try_close_identical_raw_add_suffix(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "different right operands must not be cancelled"
    );
}

#[test]
fn test_identical_raw_add_suffix_fast_path_rejects_symbolic_residual() {
    let shared = mk_var("shared");
    let lhs = mk_int_add(&mk_var("a"), &shared);
    let rhs = mk_int_add(&mk_var("b"), &shared);
    let proof = mk_var("h");

    assert!(
        try_close_identical_raw_add_suffix(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "direct cancellation must fail closed unless both residuals are concrete"
    );
}

#[test]
fn test_identical_raw_add_suffix_fast_path_rejects_satisfied_concrete_residual() {
    let shared = mk_var("shared");
    let lhs = mk_int_add(&mk_int_literal(3), &shared);
    let rhs = mk_int_add(&mk_int_literal(4), &shared);
    let proof = mk_var("h");

    assert!(
        try_close_identical_raw_add_suffix(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "direct cancellation must not derive False from a satisfied concrete comparison"
    );
}
