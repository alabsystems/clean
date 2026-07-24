// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — `is_prop` inference paths.
//!
//! Covers:
//! - `is_prop` quick path (Sort(0) inferred directly)
//! - `is_prop` full inference fallback (Pi types that fail `try_infer_type_quick`)
//! - `is_prop` returns Err on inference failure (#2208)

use super::*;

// ===== is_prop tests =====
// is_prop (tc/infer.rs) has two paths:
// 1. Quick path via try_infer_type_quick (tested elsewhere)
// 2. Full inference fallback via infer_type (UNTESTED)
// The full fallback is needed for Pi types where the body mentions the bound var.

/// Test is_prop on a simple Prop expression.
/// This exercises the quick path (Sort(0) inferred directly).
#[test]
fn test_is_prop_simple_prop() {
    use crate::env::Declaration;

    let mut env = Environment::new();
    // Add axiom p : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("env setup: add axiom p : Prop");

    let tc = TypeChecker::new(&env);

    // The correct interpretation: is_prop(P) means P is a proposition (its type is Prop).
    // P = p → typeof(p) = Prop → whnf(Prop) = Sort(0) → yes
    let p_const = Expr::const_(Name::from_string("p"), vec![]);
    assert!(
        tc.is_prop(&p_const).expect("is_prop should succeed for p"),
        "p : Prop should be a proposition (typeof(p) is Prop)"
    );

    // Prop itself is a type, not a proposition
    // P = Prop → typeof(Prop) = Type(1) → is_prop = false (Prop is a type, not a prop)
    assert!(
        !tc.is_prop(&Expr::prop())
            .expect("is_prop should succeed for Prop"),
        "Prop is Sort(0), typeof(Sort(0)) = Sort(1) ≠ Sort(0)"
    );
}

/// Test is_prop on a Pi type that requires full inference.
/// Pi types with bound variable references in the body need full infer_type
/// because try_infer_type_quick returns None for such cases.
#[test]
fn test_is_prop_pi_full_inference_fallback() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Add axiom P : Nat → Prop (a predicate)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("env setup: add axiom Nat : Type");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // P : Nat → Prop
    let p_type = Expr::pi(BinderInfo::Default, nat.clone(), Expr::prop());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: p_type,
    })
    .expect("env setup: add axiom P : Nat -> Prop");

    // n : Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("env setup: add axiom n : Nat");

    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let n_const = Expr::const_(Name::from_string("n"), vec![]);

    // P n : Prop — this is a proposition
    let p_n = Expr::app(p_const.clone(), n_const.clone());

    let tc = TypeChecker::new(&env);

    // P n should be a proposition (typeof(P n) = Prop)
    assert!(
        tc.is_prop(&p_n).expect("is_prop should succeed for P n"),
        "P n should be in Prop since P : Nat → Prop"
    );

    // P itself (Nat → Prop) should NOT be a proposition
    // typeof(Nat → Prop) = Sort(1) (Type)
    assert!(
        !tc.is_prop(&p_const).expect("is_prop should succeed for P"),
        "P : Nat → Prop is a type, not a proposition"
    );
}

/// Test is_prop returns Err when infer_type fails (#2208).
/// A dangling BVar should cause infer_type to fail, and is_prop should
/// propagate the error rather than silently returning false.
#[test]
fn test_is_prop_infer_failure_returns_error() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // BVar(0) without context — infer_type will fail (no binding at index 0)
    // try_infer_type_quick returns None for BVar, then infer_type should fail
    let dangling = Expr::bvar(0);
    assert!(
        tc.is_prop(&dangling).is_err(),
        "Dangling BVar should cause is_prop to return Err, not false"
    );
}

/// Test is_prop returns Err for unknown constant (#2208).
/// An unregistered constant should cause infer_type to fail, and is_prop
/// should propagate the error.
#[test]
fn test_is_prop_unknown_const_returns_error() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Unknown constant — not registered in environment
    let unknown = Expr::const_(Name::from_string("Unknown.Const"), vec![]);
    assert!(
        tc.is_prop(&unknown).is_err(),
        "Unknown constant should cause is_prop to return Err"
    );
}
