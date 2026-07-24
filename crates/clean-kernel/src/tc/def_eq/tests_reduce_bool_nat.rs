// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `Lean.reduceBool` and `Lean.reduceNat` native reduction.
//!
//! These test the `try_reduce_bool_nat` method in `delta_helpers.rs` which
//! approximates Lean 4's JIT native evaluation of `reduceBool`/`reduceNat`.
//! Part of #3210.

use crate::env::{ConstantInfo, ConstantKind, Environment};
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Helper: add a definition to the environment.
fn add_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Helper: add an opaque declaration to the environment.
fn add_opaque(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.kind = ConstantKind::Opaque;
    env.extend_constants_unchecked(std::iter::once(info));
}

// ============================================================================
// Lean.reduceBool tests
// ============================================================================

/// `Lean.reduceBool(myConst)` where `myConst := Bool.true` should reduce to `Bool.true`.
#[test]
fn test_reduce_bool_const_true() {
    let mut env = Environment::new();
    env.init_native_reducers();
    // myConst := Bool.true
    add_def(
        &mut env,
        "myConst",
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    let tc = TypeChecker::new(&env);

    // Build: Lean.reduceBool myConst
    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("myConst"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceBool(myConst) should reduce when myConst := Bool.true"
    );
    let result = result.unwrap();
    if let ExprKind::Const(name, _) = result.kind() {
        assert_eq!(name.to_string(), "Bool.true");
    } else {
        panic!("Expected Bool.true, got {:?}", result);
    }
}

/// `Lean.reduceBool(myConst)` where `myConst := Bool.false` should reduce to `Bool.false`.
#[test]
fn test_reduce_bool_const_false() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "myConst",
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.false"), vec![]),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("myConst"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceBool(myConst) should reduce when myConst := Bool.false"
    );
    let result = result.unwrap();
    if let ExprKind::Const(name, _) = result.kind() {
        assert_eq!(name.to_string(), "Bool.false");
    } else {
        panic!("Expected Bool.false, got {:?}", result);
    }
}

/// `Lean.reduceBool(nonexistent)` should return None (constant not in environment).
#[test]
fn test_reduce_bool_unknown_const_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("nonexistent"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceBool(nonexistent) should return None"
    );
}

/// `Lean.reduceBool` with no arguments should return None.
#[test]
fn test_reduce_bool_no_args_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let expr = Expr::const_(Name::from_string("Lean.reduceBool"), vec![]);
    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceBool with no args should return None"
    );
}

/// `Lean.reduceBool` applied to a non-Bool-valued constant should return None.
#[test]
fn test_reduce_bool_nat_valued_const_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "natConst",
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(42),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("natConst"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceBool on a Nat-valued constant should return None"
    );
}

/// `Lean.reduceBool` with a chain of definitions: `a := b`, `b := Bool.true`.
#[test]
fn test_reduce_bool_chain_definition() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "b",
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    add_def(
        &mut env,
        "a",
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceBool should follow definition chains"
    );
    let result = result.unwrap();
    if let ExprKind::Const(name, _) = result.kind() {
        assert_eq!(name.to_string(), "Bool.true");
    } else {
        panic!("Expected Bool.true, got {:?}", result);
    }
}

// ============================================================================
// Lean.reduceNat tests
// ============================================================================

/// `Lean.reduceNat(myConst)` where `myConst := 42` should reduce to Nat literal 42.
#[test]
fn test_reduce_nat_const_literal() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "myNat",
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(42),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::const_(Name::from_string("myNat"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceNat(myNat) should reduce when myNat := 42"
    );
    let result = result.unwrap();
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(42));
    } else {
        panic!("Expected Nat literal 42, got {:?}", result);
    }
}

/// `Lean.reduceNat(myConst)` where `myConst := 0` should reduce to Nat literal 0.
#[test]
fn test_reduce_nat_const_zero() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "myZero",
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(0),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::const_(Name::from_string("myZero"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceNat(myZero) should reduce when myZero := 0"
    );
    let result = result.unwrap();
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Nat literal 0, got {:?}", result);
    }
}

/// `Lean.reduceNat` with arithmetic: `myConst := Nat.add 3 4` should reduce to 7
/// (via native reducer for Nat.add + WHNF).
#[test]
fn test_reduce_nat_with_arithmetic() {
    let mut env = Environment::new();
    env.init_native_reducers();
    env.init_arith_native_reducers();

    // mySum := Nat.add 3 4
    let nat_add_expr = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [Expr::nat_lit(3), Expr::nat_lit(4)],
    );
    add_def(
        &mut env,
        "mySum",
        Expr::const_(Name::from_string("Nat"), vec![]),
        nat_add_expr,
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::const_(Name::from_string("mySum"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_some(),
        "Lean.reduceNat should handle Nat.add(3, 4)"
    );
    let result = result.unwrap();
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(7));
    } else {
        panic!("Expected Nat literal 7, got {:?}", result);
    }
}

/// `Lean.reduceNat(nonexistent)` should return None.
#[test]
fn test_reduce_nat_unknown_const_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::const_(Name::from_string("nonexistent"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceNat(nonexistent) should return None"
    );
}

/// `Lean.reduceNat` with no arguments should return None.
#[test]
fn test_reduce_nat_no_args_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let expr = Expr::const_(Name::from_string("Lean.reduceNat"), vec![]);
    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceNat with no args should return None"
    );
}

/// `Lean.reduceNat` on a Bool-valued constant should return None.
#[test]
fn test_reduce_nat_bool_valued_const_returns_none() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_def(
        &mut env,
        "boolConst",
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    let tc = TypeChecker::new(&env);

    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::const_(Name::from_string("boolConst"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(
        result.is_none(),
        "Lean.reduceNat on a Bool-valued constant should return None"
    );
}

/// Other native reducers (Nat.decEq etc.) should still work alongside reduceBool/reduceNat.
#[test]
fn test_other_native_reducers_unaffected() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    // Nat.decEq 3 3 should still work
    let nat_dec_eq_app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.decEq"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(3),
    );

    let result = tc.reduce_native_for_test(&nat_dec_eq_app);
    assert!(result.is_some(), "Nat.decEq should still fire");
}

/// `Lean.reduceBool` applied to a non-constant (e.g., a literal) should
/// try to WHNF the argument directly.
#[test]
fn test_reduce_bool_applied_to_literal_bool_true() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    // Lean.reduceBool(Bool.true) — argument is already a constructor
    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceBool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );

    let result = tc.reduce_native_for_test(&expr);
    // Bool.true is not a definition (no value to unfold), so WHNF returns it as-is.
    // It IS a Const with name "Bool.true", which passes the check.
    assert!(
        result.is_some(),
        "Lean.reduceBool(Bool.true) should succeed"
    );
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(name.to_string(), "Bool.true");
    }
}

/// `Lean.reduceNat` applied to a Nat literal directly should reduce.
#[test]
fn test_reduce_nat_applied_to_literal() {
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    // Lean.reduceNat(42) — argument is already a Nat literal
    let expr = Expr::app(
        Expr::const_(Name::from_string("Lean.reduceNat"), vec![]),
        Expr::nat_lit(42),
    );

    let result = tc.reduce_native_for_test(&expr);
    assert!(result.is_some(), "Lean.reduceNat(42) should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(42));
    }
}
