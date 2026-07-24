// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for trustedArith axiom and term creation.
//!
//! Modeled after trusted_ay.rs. Verifies:
//! 1. Axiom initialization creates correct polymorphic type
//! 2. Term creation produces correctly-typed terms
//! 3. Counter tracking increments only for actual trustedArith usage
//! 4. Fallback to sorry when trustedArith not initialized
//!
//! Part of #1144: sorry enforcement gap — trustedArith had zero test coverage.

use super::*;
use crate::tactic::arith_linarith::{
    arith_proof_count, create_trusted_arith_term, reset_arith_counter,
};
use clean_kernel::expr::ExprKind;
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use serial_test::serial;

/// Test 1: init_trusted_arith() creates correct axiom type
///
/// Expected: trustedArith.{u} : {α : Sort u} → α
/// Same polymorphic type as trustedAy.
#[test]
fn test_init_trusted_arith_axiom_type() {
    let mut env = Environment::new();

    let result = env.init_trusted_arith();
    assert!(result.is_ok(), "init_trusted_arith should succeed");

    let trusted_arith_const = env.get_const(&Name::from_string("trustedArith"));
    assert!(
        trusted_arith_const.is_some(),
        "trustedArith axiom should exist after init"
    );

    let info = trusted_arith_const.unwrap();

    // Check universe parameters: should have one parameter 'u'
    assert_eq!(
        info.level_params.len(),
        1,
        "trustedArith should have 1 universe parameter"
    );
    assert_eq!(
        info.level_params[0].to_string(),
        "u",
        "universe parameter should be named 'u'"
    );

    // Verify it's an axiom (no value)
    assert!(
        info.value.is_none(),
        "trustedArith should be an axiom (no value)"
    );

    // The type should be: Π {α : Sort u}, α
    let ty = &info.type_;
    assert!(
        matches!(ty.kind(), ExprKind::Pi(_, _, _)),
        "trustedArith type should be a Pi"
    );

    if let ExprKind::Pi(binder_info, binder_ty, body) = ty.kind() {
        assert!(
            binder_info.info == BinderInfo::Implicit,
            "trustedArith binder should be implicit"
        );
        assert!(
            matches!(binder_ty.kind(), ExprKind::Sort(_)),
            "trustedArith domain should be Sort"
        );
        assert!(
            matches!(body.kind(), ExprKind::BVar(0)),
            "trustedArith body should be BVar(0)"
        );
    }
}

/// Test 2: init_trusted_arith() is idempotent
#[test]
fn test_init_trusted_arith_idempotent() {
    let mut env = Environment::new();

    env.init_trusted_arith()
        .expect("first init_trusted_arith should succeed");
    env.init_trusted_arith()
        .expect("second init_trusted_arith should succeed (idempotent)");

    let trusted_arith_const = env.get_const(&Name::from_string("trustedArith"));
    assert!(
        trusted_arith_const.is_some(),
        "trustedArith constant should exist in environment"
    );
}

/// Test 3: create_trusted_arith_term produces correctly-typed term
///
/// When trustedArith axiom is initialized, create_trusted_arith_term should:
/// - Produce @trustedArith.{u} goal_ty where u is the correct universe level
/// - Increment ARITH_PROOF_COUNTER
/// - NOT increment SORRY_COUNTER
///
/// For goal_ty = Prop (Sort 0), the correct universe level is 1 because
/// Prop : Sort 1 (i.e., Prop lives in Type). trustedArith.{u} : {α : Sort u} → α
/// requires α : Sort u, so for α = Prop we need u = 1.
#[test]
#[serial]
fn test_create_trusted_arith_term_with_axiom() {
    let mut env = Environment::new();
    env.init_trusted_arith().unwrap();

    reset_arith_counter();
    reset_sorry_counter();

    let goal_ty = Expr::prop(); // Prop = Sort 0, which has type Sort 1
    let term = create_trusted_arith_term(&env, &goal_ty);

    assert_eq!(arith_proof_count(), 1, "ARITH counter should increment");
    assert_eq!(sorry_count(), 0, "SORRY counter should NOT increment");

    // Verify term structure: App(Const(trustedArith, [u]), goal_ty)
    // where u = infer_sort(Prop) = 1 (since Prop : Sort 1)
    if let ExprKind::App(func, arg) = term.kind() {
        if let ExprKind::Const(name, levels) = func.kind() {
            assert_eq!(
                name.to_string(),
                "trustedArith",
                "Function should be trustedArith"
            );
            assert_eq!(levels.len(), 1, "Should have 1 universe level");
            // Prop : Sort 1, so u = Succ(Zero) = 1
            assert!(
                matches!(&levels[0], Level::Succ(inner) if matches!(inner.as_ref(), Level::Zero)),
                "Universe level should be 1 (Succ(Zero)) for Prop goal, got {:?}",
                levels[0]
            );
        } else {
            panic!("Expected trustedArith constant, got {:?}", func);
        }

        assert!(
            matches!(arg.kind(), ExprKind::Sort(_)),
            "Argument should be Prop/Sort"
        );
    } else {
        panic!("Expected App, got {:?}", term);
    }
}

/// Test 4: create_trusted_arith_term falls back to sorry when axiom not initialized
///
/// When trustedArith axiom is NOT initialized, create_trusted_arith_term should:
/// - Fall back to creating a sorry term
/// - NOT increment ARITH_PROOF_COUNTER
/// - Increment SORRY_COUNTER instead
#[test]
#[serial]
fn test_create_trusted_arith_term_fallback_to_sorry() {
    // Use Environment::default() (bare struct) instead of Environment::new()
    // because new() now initializes trustedArith by default (since W1-1275).
    let env = Environment::default();

    reset_arith_counter();
    reset_sorry_counter();

    let goal_ty = Expr::prop();
    let _term = create_trusted_arith_term(&env, &goal_ty);

    assert_eq!(arith_proof_count(), 0, "ARITH counter should NOT increment");
    assert_eq!(
        sorry_count(),
        1,
        "SORRY counter should increment for fallback"
    );
}

/// Test 5: Counter isolation between tests
#[test]
#[serial]
fn test_arith_counter_isolation() {
    let mut env = Environment::new();
    env.init_trusted_arith().unwrap();

    let goal_ty = Expr::prop();
    let term1 = create_trusted_arith_term(&env, &goal_ty);
    let term2 = create_trusted_arith_term(&env, &goal_ty);
    assert!(
        !matches!(term1.kind(), ExprKind::BVar(..)),
        "arith term should not be a bound variable"
    );
    assert!(
        !matches!(term2.kind(), ExprKind::BVar(..)),
        "arith term should not be a bound variable"
    );

    reset_arith_counter();
    assert_eq!(arith_proof_count(), 0, "Counter should be 0 after reset");

    let term3 = create_trusted_arith_term(&env, &goal_ty);
    assert!(
        !matches!(term3.kind(), ExprKind::BVar(..)),
        "arith term should not be a bound variable after reset"
    );
    assert_eq!(arith_proof_count(), 1, "Counter should be 1 after one term");
}

/// Test 6: trustedArith term type checks correctly
#[test]
#[serial]
fn test_trusted_arith_term_type_checks() {
    let mut env = Environment::new();
    env.init_trusted_arith().unwrap();
    env.init_true_false().unwrap(); // Add True type for a concrete Prop

    let goal_ty = Expr::const_(Name::from_string("True"), vec![]);
    let term = create_trusted_arith_term(&env, &goal_ty);

    let tc = TypeChecker::new(&env);
    let inferred_ty = tc.infer_type(&term);

    assert!(
        inferred_ty.is_ok(),
        "trustedArith term should type check: {:?}",
        inferred_ty.err()
    );
    let inferred = inferred_ty.unwrap();

    if let ExprKind::Const(name, _) = inferred.kind() {
        assert_eq!(name.to_string(), "True", "Inferred type should be True");
    } else {
        panic!("Inferred type should be Const True, got {:?}", inferred);
    }
}
