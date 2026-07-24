// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};
use num_bigint::BigInt;

use super::super::expr_builders_real_downcast::extract_int_from_real_endpoint;
use super::super::theory_lemma_lra_additive::mk_int_add;
use super::*;

fn mk_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Build `Nat.zero` in constructor form.
fn mk_nat_zero_ctor() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

/// Build `Nat.succ(n)` in constructor form.
fn mk_nat_succ_ctor(inner: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        inner.clone(),
    )
}

/// Build `Int.ofNat(n)` with a constructor-form Nat argument.
fn mk_int_ofnat_ctor(nat_expr: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        nat_expr.clone(),
    )
}

/// Build `Int.negSucc(n)` with a constructor-form Nat argument.
fn mk_int_negsucc_ctor(nat_expr: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        nat_expr.clone(),
    )
}

fn mk_nf(atoms: Vec<Expr>, constant: i64) -> IntAddNf {
    let constant_big = BigInt::from(constant);
    let constant_terms = if constant == 0 {
        Vec::new()
    } else {
        vec![mk_int_literal(constant)]
    };
    IntAddNf {
        atoms,
        constant_terms,
        constant: constant_big,
    }
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
fn test_flatten_concrete_only() {
    let expr = mk_int_literal(5);
    let nf = IntAddNf::from_expr(&expr);
    assert!(nf.atoms.is_empty());
    assert_eq!(nf.constant_terms.len(), 1);
    assert_eq!(nf.constant, BigInt::from(5));
}

#[test]
fn test_flatten_single_atom() {
    let x = mk_var("x");
    let nf = IntAddNf::from_expr(&x);
    assert_eq!(nf.atoms.len(), 1);
    assert!(nf.constant_terms.is_empty());
    assert_eq!(nf.constant, BigInt::from(0));
}

#[test]
fn test_flatten_add_with_concrete() {
    let x = mk_var("x");
    let three = mk_int_literal(3);
    let expr = mk_int_add(&x, &three);
    let nf = IntAddNf::from_expr(&expr);
    assert_eq!(nf.atoms.len(), 1);
    assert_eq!(nf.constant_terms.len(), 1);
    assert_eq!(nf.constant, BigInt::from(3));
}

#[test]
fn test_flatten_nested_add() {
    let x = mk_var("x");
    let y = mk_var("y");
    let one = mk_int_literal(1);
    let inner = mk_int_add(&x, &one);
    let expr = mk_int_add(&inner, &y);
    let nf = IntAddNf::from_expr(&expr);
    assert_eq!(nf.atoms.len(), 2);
    assert_eq!(nf.constant_terms.len(), 1);
    assert_eq!(nf.constant, BigInt::from(1));
}

#[test]
fn test_close_shape_full_shared() {
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_nf(vec![x.clone(), y.clone()], 4);
    let rhs = mk_nf(vec![x, y], 3);
    let shape = build_close_shape(&lhs, &rhs);
    assert!(shape.lhs_only.is_empty());
    assert!(shape.rhs_only.is_empty());
    assert_eq!(shape.shared.len(), 2);
    assert_eq!(shape.lhs_const, BigInt::from(4));
    assert_eq!(shape.rhs_const, BigInt::from(3));
    assert!(shape.residual_is_concrete_contradiction(CmpOp::Le));
}

#[test]
fn test_close_shape_partial_shared() {
    let x = mk_var("x");
    let z = mk_var("z");
    let w = mk_var("w");
    let lhs = mk_nf(vec![x.clone(), z.clone()], 0);
    let rhs = mk_nf(vec![x, w.clone()], 0);
    let shape = build_close_shape(&lhs, &rhs);
    assert_eq!(shape.lhs_only.len(), 1);
    assert_eq!(shape.rhs_only.len(), 1);
    assert_eq!(shape.shared.len(), 1);
    assert!(!shape.residual_is_concrete_contradiction(CmpOp::Le));
}

#[test]
fn test_close_shape_motivating_example() {
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_nf(vec![x.clone(), y.clone()], 4);
    let rhs = mk_nf(vec![x, y], 3);
    let shape = build_close_shape(&lhs, &rhs);
    assert!(shape.lhs_only.is_empty());
    assert!(shape.rhs_only.is_empty());
    assert_eq!(shape.shared.len(), 2);
    assert!(shape.residual_is_concrete_contradiction(CmpOp::Le));
}

#[test]
fn test_to_expr_roundtrip() {
    let x = mk_var("x");
    let y = mk_var("y");
    let nf = mk_nf(vec![x, y], 5);
    let expr = nf.to_expr();
    let nf2 = IntAddNf::from_expr(&expr);
    assert_eq!(nf2.atoms.len(), 2);
    assert_eq!(nf2.constant, BigInt::from(5));
}

#[test]
fn test_mk_int_cancel_add_right_builds_expr() {
    let a = mk_var("a");
    let b = mk_var("b");
    let c = mk_var("c");
    let h = mk_var("h");
    let result = mk_int_cancel_add_right(CmpOp::Le, &a, &b, &c, &h);
    if let ExprKind::App(_, _) = result.kind() {
    } else {
        panic!("Expected App expression from cancellation lemma");
    }
}

#[test]
fn test_close_shape_lt_contradiction() {
    let lhs = mk_nf(vec![], 3);
    let rhs = mk_nf(vec![], 3);
    let shape = build_close_shape(&lhs, &rhs);
    assert!(!shape.residual_is_concrete_contradiction(CmpOp::Le));
    assert!(shape.residual_is_concrete_contradiction(CmpOp::Lt));
}

#[test]
fn test_negative_constant() {
    let neg3 = mk_int_literal(-3);
    let nf = IntAddNf::from_expr(&neg3);
    assert!(nf.atoms.is_empty());
    assert_eq!(nf.constant, BigInt::from(-3));
}

#[test]
fn test_try_close_int_additive_nf_motivating_shape_returns_false_proof() {
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_int_add(&mk_int_literal(4), &mk_int_add(&x, &y));
    let rhs = mk_int_add(&mk_int_literal(3), &mk_int_add(&x, &y));
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("motivating symbolic closeout should now reconstruct");

    assert!(
        expr_contains_const(&false_proof, "Int.le_of_add_le_add_right"),
        "closeout should cancel the shared additive suffix"
    );
    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "closeout should finish with the concrete Int contradiction builder"
    );
}

// --- Constructor-form Nat constant tests (#2603) ---

#[test]
fn test_flatten_constructor_form_zero() {
    // Int.ofNat(Nat.zero) should be recognized as concrete 0
    let expr = mk_int_ofnat_ctor(&mk_nat_zero_ctor());
    let nf = IntAddNf::from_expr(&expr);
    assert!(
        nf.atoms.is_empty(),
        "constructor-form zero should not be an atom"
    );
    assert_eq!(nf.constant, BigInt::from(0));
}

#[test]
fn test_flatten_constructor_form_one() {
    // Int.ofNat(Nat.succ(Nat.zero)) should be recognized as concrete 1
    let one = mk_nat_succ_ctor(&mk_nat_zero_ctor());
    let expr = mk_int_ofnat_ctor(&one);
    let nf = IntAddNf::from_expr(&expr);
    assert!(
        nf.atoms.is_empty(),
        "constructor-form 1 should not be an atom"
    );
    assert_eq!(nf.constant_terms.len(), 1);
    assert_eq!(nf.constant, BigInt::from(1));
}

#[test]
fn test_flatten_constructor_form_negsucc() {
    // Int.negSucc(Nat.zero) should be recognized as concrete -1
    let expr = mk_int_negsucc_ctor(&mk_nat_zero_ctor());
    let nf = IntAddNf::from_expr(&expr);
    assert!(
        nf.atoms.is_empty(),
        "constructor-form -1 should not be an atom"
    );
    assert_eq!(nf.constant, BigInt::from(-1));
}

#[test]
fn test_flatten_constructor_form_succ_of_literal() {
    // Int.ofNat(Nat.succ(Nat.lit(2))) — mixed constructor/literal form = 3
    let inner = Expr::nat_lit(2);
    let three = mk_nat_succ_ctor(&inner);
    let expr = mk_int_ofnat_ctor(&three);
    let nf = IntAddNf::from_expr(&expr);
    assert!(
        nf.atoms.is_empty(),
        "mixed constructor/literal Nat should be concrete"
    );
    assert_eq!(nf.constant, BigInt::from(3));
}

#[test]
fn test_close_constructor_form_residual_contradiction() {
    // After suffix cancellation: residual Int.ofNat(Nat.succ(Nat.zero)) <= Int.ofNat(Nat.zero)
    // i.e., 1 <= 0 — should be a concrete contradiction
    let x = mk_var("x");
    let one_ctor = mk_int_ofnat_ctor(&mk_nat_succ_ctor(&mk_nat_zero_ctor()));
    let zero_ctor = mk_int_ofnat_ctor(&mk_nat_zero_ctor());
    let lhs = mk_int_add(&one_ctor, &x);
    let rhs = mk_int_add(&zero_ctor, &x);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("constructor-form residual contradiction should close");

    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "closeout should finish with the concrete Int contradiction builder"
    );
}

#[test]
fn test_close_constructor_form_strict_equal_residual_contradiction() {
    // After suffix cancellation: residual Int.ofNat(Nat.succ(Nat.zero)) <
    // Int.ofNat(Nat.succ(Nat.zero)), i.e. 1 < 1 — strict equality is
    // contradictory and must close.
    let x = mk_var("x");
    let one_ctor = mk_int_ofnat_ctor(&mk_nat_succ_ctor(&mk_nat_zero_ctor()));
    let lhs = mk_int_add(&one_ctor, &x);
    let rhs = mk_int_add(&one_ctor, &x);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Lt, &lhs, &rhs, &proof)
        .expect("constructor-form strict equality should close");

    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "strict constructor-form closeout should finish with the concrete Int contradiction builder"
    );
}

#[test]
fn test_real_downcast_constructor_form_feeds_additive_closeout() {
    // Regression: Real.ofNat(Nat.succ(Nat.zero)) downcasts to Int.ofNat(Nat.succ(Nat.zero))
    // which must be recognized as concrete 1 by the additive closeout.
    let real_one = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        mk_nat_succ_ctor(&mk_nat_zero_ctor()),
    );
    let real_zero = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        mk_nat_zero_ctor(),
    );

    let int_one = extract_int_from_real_endpoint(&real_one)
        .expect("Real.ofNat(Nat.succ(Nat.zero)) should downcast");
    let int_zero =
        extract_int_from_real_endpoint(&real_zero).expect("Real.ofNat(Nat.zero) should downcast");

    // Feed the downcasted Int expressions into additive closeout: (1 + x) <= (0 + x)
    let x = mk_var("x");
    let lhs = mk_int_add(&int_one, &x);
    let rhs = mk_int_add(&int_zero, &x);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("Real downcast constructor-form should close via additive NF");

    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "bridge regression: Real downcast path should avoid trust boundary"
    );
}

#[test]
fn test_real_downcast_constructor_form_strict_equal_feeds_additive_closeout() {
    // Regression boundary: Real.ofNat(Nat.succ(Nat.zero)) downcasts to the same
    // constructor-form Int value on both sides, so strict equality must still
    // close as 1 < 1.
    let real_one = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        mk_nat_succ_ctor(&mk_nat_zero_ctor()),
    );

    let int_one = extract_int_from_real_endpoint(&real_one)
        .expect("Real.ofNat(Nat.succ(Nat.zero)) should downcast");

    let x = mk_var("x");
    let lhs = mk_int_add(&int_one, &x);
    let rhs = mk_int_add(&int_one, &x);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Lt, &lhs, &rhs, &proof)
        .expect("Real downcast constructor-form strict equality should close via additive NF");

    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "bridge regression: Real downcast strict equality should avoid trust boundary"
    );
}

// --- Algorithm audit boundary tests (#2722 Phase 3) ---

/// Verify that `mk_int_literal` / `extract_int_literal` roundtrip correctly
/// for a range of values including negatives and the boundary at -1.
///
/// This catches potential off-by-one in the `Int.negSucc(n) = -(n+1)` encoding.
#[test]
fn test_int_literal_roundtrip_boundary_values() {
    let test_cases: &[i64] = &[0, 1, -1, 2, -2, 127, -128, 1000, -1000];
    for &value in test_cases {
        let expr = mk_int_literal(value);
        let extracted = extract_int_literal(&expr)
            .unwrap_or_else(|| panic!("extract_int_literal should succeed for {value}"));
        assert_eq!(
            extracted,
            BigInt::from(value),
            "roundtrip failed for mk_int_literal({value})"
        );
    }
}

/// Verify multiset matching in `build_close_shape` when both sides have
/// duplicate atoms. LHS = [x, x, y], RHS = [x, y, y]: shared = [x, y],
/// lhs_only = [x], rhs_only = [y].
///
/// This tests that the O(n*m) matching uses `break` correctly to avoid
/// consuming multiple RHS slots for a single LHS atom.
#[test]
fn test_close_shape_multiset_with_duplicates() {
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_nf(vec![x.clone(), x.clone(), y.clone()], 0);
    let rhs = mk_nf(vec![x.clone(), y.clone(), y.clone()], 0);
    let shape = build_close_shape(&lhs, &rhs);
    assert_eq!(shape.shared.len(), 2, "shared should be [x, y]");
    assert_eq!(shape.lhs_only.len(), 1, "lhs_only should be [x]");
    assert_eq!(shape.rhs_only.len(), 1, "rhs_only should be [y]");
}

/// Verify `residual_is_concrete_contradiction` at exact Le/Lt boundary.
///
/// Le: `lhs <= rhs` is contradictory iff `lhs > rhs` (strict).
/// Lt: `lhs < rhs` is contradictory iff `lhs >= rhs`.
///
/// Test with lhs_const=5, rhs_const=5: Le is OK (5<=5), Lt is contradiction (5<5).
/// Test with lhs_const=5, rhs_const=4: both are contradictions.
/// Test with lhs_const=4, rhs_const=5: neither is a contradiction.
#[test]
fn test_residual_contradiction_le_lt_boundary() {
    // 5 <= 5: not contradictory; 5 < 5: contradictory
    let equal = build_close_shape(&mk_nf(vec![], 5), &mk_nf(vec![], 5));
    assert!(
        !equal.residual_is_concrete_contradiction(CmpOp::Le),
        "5 <= 5 should NOT be a contradiction"
    );
    assert!(
        equal.residual_is_concrete_contradiction(CmpOp::Lt),
        "5 < 5 SHOULD be a contradiction"
    );

    // 5 <= 4: contradictory; 5 < 4: contradictory
    let lhs_bigger = build_close_shape(&mk_nf(vec![], 5), &mk_nf(vec![], 4));
    assert!(
        lhs_bigger.residual_is_concrete_contradiction(CmpOp::Le),
        "5 <= 4 SHOULD be a contradiction"
    );
    assert!(
        lhs_bigger.residual_is_concrete_contradiction(CmpOp::Lt),
        "5 < 4 SHOULD be a contradiction"
    );

    // 4 <= 5: not contradictory; 4 < 5: not contradictory
    let lhs_smaller = build_close_shape(&mk_nf(vec![], 4), &mk_nf(vec![], 5));
    assert!(
        !lhs_smaller.residual_is_concrete_contradiction(CmpOp::Le),
        "4 <= 5 should NOT be a contradiction"
    );
    assert!(
        !lhs_smaller.residual_is_concrete_contradiction(CmpOp::Lt),
        "4 < 5 should NOT be a contradiction"
    );
}
