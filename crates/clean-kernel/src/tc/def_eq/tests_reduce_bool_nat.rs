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

/// Declare `Lean.reduceBool`/`Lean.reduceNat` as Lean's `Init` does: an opaque
/// whose value is the identity (`opaque Lean.reduceBool (b : Bool) : Bool :=
/// b`). The rule `reduceBool c ≡ c` is justified by that value and by nothing
/// else (`env/native_fold_authority.rs`), so an environment that does not
/// declare them — every one these tests built before 2026-09-26 — no longer
/// evaluates them.
fn install_reduce_identities(env: &mut Environment) {
    for (name, ty) in [("Lean.reduceBool", "Bool"), ("Lean.reduceNat", "Nat")] {
        let ty = Expr::const_(Name::from_string(ty), vec![]);
        let arrow = Expr::pi(crate::expr::BinderInfo::Default, ty.clone(), ty.clone());
        let id = Expr::lam(crate::expr::BinderInfo::Default, ty, Expr::bvar(0));
        add_opaque(env, name, arrow, id);
    }
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    let mut env = Environment::with_prelude();
    env.init_native_reducers();
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    let mut env = Environment::with_prelude();
    env.init_native_reducers();
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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
    install_reduce_identities(&mut env);
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

// ============================================================================
// ESTABLISHED: whnf DOES consult native reducers for a NULLARY constant.
//
// Written to test the hypothesis that the `reduce_native` pre-check in
// `tc/whnf.rs` — which lives inside the `App` branch — leaves nullary constants
// unreachable. IT DOES NOT: this test passes. Nullary reduction works, so that
// hypothesis is refuted and the `Int32.minValue` blowup is NOT a missing
// consult here. Keep this test: it pins the behaviour the next investigation
// would otherwise re-suspect.
//
// This matters because `Int32.minValue` is exactly such a constant, and its
// failure to reduce to a literal is what makes `import Init.GrindInstances`
// cost 12 GB+: the kernel falls back to unfolding `Int32.ofInt` and iterating
// `Nat.rec` unarily over ~2^31.
//
// The reducer below deliberately returns a value DIFFERENT from the
// definition, so the assertion discriminates cleanly:
//   42 => the native reducer fired
//    7 => delta-unfolding won and the reducer was never consulted
// ============================================================================

fn nullary_probe_reducer(args: &[&Expr]) -> Option<Expr> {
    if !args.is_empty() {
        return None;
    }
    Some(Expr::nat_lit(42))
}

#[test]
fn test_whnf_consults_native_reducer_for_nullary_const() {
    let mut env = Environment::new();
    env.init_native_reducers();
    install_reduce_identities(&mut env);

    // `ZeroAry.k : Nat := 7`, with a native reducer claiming 42.
    add_def(
        &mut env,
        "ZeroAry.k",
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(7),
    );
    env.register_native_reducer(
        Name::from_string("ZeroAry.k"),
        nullary_probe_reducer as fn(args: &[&Expr]) -> Option<Expr>,
    );

    let tc = TypeChecker::new(&env);
    let bare = Expr::const_(Name::from_string("ZeroAry.k"), vec![]);
    let reduced = tc.whnf(&bare);

    // RE-DECIDED 2026-09-26 (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`):
    // this used to assert 42 — a reducer overriding the head's own δ answer
    // (7), which is the very shape that let a user definition prove `False`.
    // whnf still CONSULTS the registry for a nullary constant (the
    // Int32.minValue path), and native-fold authority now refuses a reducer
    // whose head the environment does not hold canonically, so δ decides.
    match reduced.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            assert_eq!(
                n.to_u64(),
                Some(7),
                "whnf of a user nullary Const returned {n:?}: 42 means a native \
                 reducer overrode the constant's own definition"
            );
        }
        other => panic!("expected a Nat literal from whnf, got {other:?}"),
    }
}
