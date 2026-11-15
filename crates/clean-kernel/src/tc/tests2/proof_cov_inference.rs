// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — `is_prop` inference paths.
//!
//! Covers:
//! - `is_prop` quick path (Sort(0) inferred directly)
//! - `is_prop` full inference fallback (Pi types that fail `try_infer_type_quick`)
//! - `is_prop` returns Err on inference failure (#2208)
//! - `is_prop` returns Err(ExpectedSort) when the type of the type is not a sort
//!   (leanprover/lean4#14807), on both paths

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

    // P itself has type `Nat → Prop`, which is not a sort. Before the
    // `is_prop`-requires-a-sort guard (leanprover/lean4#14807) this answered
    // `Ok(false)` ("not a proposition"); the guard makes it err at
    // `ensure_sort`, matching Lean v4.33.1's `is_prop`. (This flips the
    // former `!is_prop(P)` assertion, which the guard makes false — see
    // `kernel-defensive-invariants-v4331`.)
    assert!(
        matches!(tc.is_prop(&p_const), Err(TypeError::ExpectedSort { .. })),
        "is_prop(P) with P : Nat → Prop (type not a sort) must be Err(ExpectedSort), got {:?}",
        tc.is_prop(&p_const)
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

// ===== is_prop requires a Sort (Lean 4 v4.33.1, leanprover/lean4#14807) =====
// Lean's `is_prop` is `ensure_sort(infer_type(e))`: a type-of-type that does
// not whnf to a sort is an ill-formed type, so `is_prop` errors instead of
// answering "not a proposition". `Ok(false)` there would let projection typing
// skip its Prop-only field guard.

/// `A : Type` and `a : A`, the smallest environment with a term whose inferred
/// type is not a sort.
fn env_with_a_term_of_a_non_sort_type() -> Environment {
    use crate::env::Declaration;

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("env setup: add axiom A : Type");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .expect("env setup: add axiom a : A");
    env
}

/// `is_prop a` with `a : A`: the type of `a` is the constant `A`, which does
/// not whnf to a sort. Quick inference answers here, so this is the quick path.
#[test]
fn is_prop_errors_on_a_non_sort_type_of_type() {
    let env = env_with_a_term_of_a_non_sort_type();
    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    assert!(
        tc.try_infer_type_quick(&a).is_some(),
        "subject: quick inference must answer for `a`, so this test drives the quick path"
    );
    let result = tc.is_prop(&a);
    assert!(
        matches!(result, Err(TypeError::ExpectedSort { .. })),
        "is_prop(a) with a : A (A not a sort) must be Err(ExpectedSort), got {result:?}"
    );
}

/// `is_prop (fun (x : A) => x)`: quick inference declines (its body is a loose
/// bound variable), so this drives the full-inference path. The inferred type
/// `A → A` is a Pi, not a sort.
#[test]
fn is_prop_errors_on_a_non_sort_type_of_type_full_inference_path() {
    let env = env_with_a_term_of_a_non_sort_type();
    let tc = TypeChecker::new(&env);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let id_a = Expr::lam(BinderInfo::Default, a_ty, Expr::bvar(0));
    assert!(
        tc.try_infer_type_quick(&id_a).is_none(),
        "subject: quick inference must decline `fun x : A => x`, so this test drives the full path"
    );
    let result = tc.is_prop(&id_a);
    assert!(
        matches!(result, Err(TypeError::ExpectedSort { .. })),
        "is_prop(fun x : A => x) must be Err(ExpectedSort), got {result:?}"
    );
}

/// Negative control: `SProp` is a sort in Clean (the type-of-type invariant in
/// `tc/infer.rs` admits `Sort | SProp`), so the sort requirement does not refuse
/// a strict proposition; its `is_prop` verdict is the one it had before.
#[test]
fn is_prop_accepts_sprop_as_a_sort() {
    use crate::mode::CleanMode;

    let env = Environment::with_mode(CleanMode::Impredicative);
    let tc = TypeChecker::with_mode(&env, CleanMode::Impredicative);
    let squash_prop = Expr::from_kind(ExprKind::Squash(std::sync::Arc::new(Expr::prop())));
    let result = tc.is_prop(&squash_prop);
    assert!(
        matches!(result, Ok(false)),
        "is_prop(Squash Prop) (type SProp) must stay Ok(false), got {result:?}"
    );
}
