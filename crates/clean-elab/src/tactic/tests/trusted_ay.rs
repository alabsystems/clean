// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for trustedAy axiom and term creation.
//!
//! Issue #1213: Verify the trustedAy infrastructure works correctly:
//! 1. Axiom initialization creates correct polymorphic type
//! 2. Term creation produces correctly-typed terms
//! 3. Counter tracking increments only for actual trustedAy usage
//! 4. Fallback to the current non-trusted stub when trustedAy is absent

use super::*;
use crate::tactic::smt::{self as smt, ay_proof_count, reset_ay_counter};
use clean_kernel::expr::ExprKind;
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use serial_test::serial;

/// Test 1: init_trusted_ay() creates correct axiom type
///
/// Expected: trustedAy.{u} : {α : Sort u} → α
/// This is a polymorphic axiom that can produce a term of any type.
#[test]
fn test_init_trusted_ay_axiom_type() {
    let mut env = Environment::new();

    // Should succeed
    let result = env.init_trusted_ay();
    assert!(result.is_ok(), "init_trusted_ay should succeed");

    // Check axiom exists
    let trusted_ay_const = env.get_const(&Name::from_string("trustedAy"));
    assert!(
        trusted_ay_const.is_some(),
        "trustedAy axiom should exist after init"
    );

    let info = trusted_ay_const.unwrap();

    // Check universe parameters: should have one parameter 'u'
    assert_eq!(
        info.level_params.len(),
        1,
        "trustedAy should have 1 universe parameter"
    );
    assert_eq!(
        info.level_params[0].to_string(),
        "u",
        "universe parameter should be named 'u'"
    );

    // Verify it's an axiom (no value)
    assert!(
        info.value.is_none(),
        "trustedAy should be an axiom (no value)"
    );

    // The type should be: Π {α : Sort u}, α
    // Which is represented as: Pi(Implicit, Sort(Param("u")), BVar(0))
    let ty = &info.type_;
    assert!(
        matches!(ty.kind(), ExprKind::Pi(_, _, _)),
        "trustedAy type should be a Pi"
    );

    if let ExprKind::Pi(binder_info, binder_ty, body) = ty.kind() {
        // Binder should be implicit
        assert!(
            binder_info.info == BinderInfo::Implicit,
            "trustedAy binder should be implicit"
        );

        // Domain should be Sort(Param("u"))
        assert!(
            matches!(binder_ty.kind(), ExprKind::Sort(_)),
            "trustedAy domain should be Sort"
        );

        // Body should be BVar(0) referring to the bound type
        assert!(
            matches!(body.kind(), ExprKind::BVar(0)),
            "trustedAy body should be BVar(0)"
        );
    }
}

/// Test 2: init_trusted_ay() is idempotent
#[test]
fn test_init_trusted_ay_idempotent() {
    let mut env = Environment::new();

    // First call
    env.init_trusted_ay()
        .expect("first init_trusted_ay should succeed");

    // Second call should also succeed (idempotent)
    env.init_trusted_ay()
        .expect("second init_trusted_ay should succeed (idempotent)");

    // Should still have exactly one trustedAy declaration
    let trusted_ay_const = env.get_const(&Name::from_string("trustedAy"));
    assert!(
        trusted_ay_const.is_some(),
        "trustedAy constant should exist in environment"
    );
}

/// Test 3: create_trusted_ay_term produces correctly-typed term
///
/// When trustedAy axiom is initialized, create_trusted_ay_term should:
/// - Infer the correct universe level from goal_ty's sort
/// - Increment AY_PROOF_COUNTER
///
/// For goal_ty = Prop (Sort 0), the correct universe level is 1 because
/// Prop : Sort 1 (i.e., Prop lives in Type). trustedAy.{u} : {α : Sort u} → α
/// requires α : Sort u, so for α = Prop we need u = 1.
#[test]
#[serial]
fn test_create_trusted_ay_term_with_axiom() {
    let mut env = Environment::new();
    env.init_trusted_ay().unwrap();

    // Reset counters for isolation
    reset_ay_counter();
    reset_sorry_counter();

    let goal_ty = Expr::prop(); // Prop = Sort 0, which has type Sort 1

    // Create trustedAy term
    let term = smt::create_trusted_ay_term(&env, &goal_ty);

    // Verify Ay counter incremented
    assert_eq!(ay_proof_count(), 1, "Ay counter should increment");
    assert_eq!(sorry_count(), 0, "Sorry counter should NOT increment");

    // Verify term structure: should be App(Const(trustedAy, [u]), goal_ty)
    // where u = infer_sort(Prop) = 1 (since Prop : Sort 1)
    if let ExprKind::App(func, arg) = term.kind() {
        // Check function is trustedAy constant
        if let ExprKind::Const(name, levels) = func.kind() {
            assert_eq!(
                name.to_string(),
                "trustedAy",
                "Function should be trustedAy"
            );
            assert_eq!(levels.len(), 1, "Should have 1 universe level");
            // Prop : Sort 1, so u = Succ(Zero) = 1
            assert!(
                matches!(&levels[0], Level::Succ(inner) if matches!(inner.as_ref(), Level::Zero)),
                "Universe level should be 1 (Succ(Zero)) for Prop goal, got {:?}",
                levels[0]
            );
        } else {
            panic!("Expected trustedAy constant, got {:?}", func);
        }

        // Check argument is goal_ty
        assert!(
            matches!(arg.kind(), ExprKind::Sort(_)),
            "Argument should be Prop/Sort"
        );
    } else {
        panic!("Expected App, got {:?}", term);
    }
}

/// Test 4: create_trusted_ay_term falls back to the SMT proof stub when
/// trustedAy is not initialized.
///
/// When trustedAy axiom is NOT initialized, create_trusted_ay_term should:
/// - Fall back to the current `SMT_PROOF` typed stub
/// - NOT increment AY_PROOF_COUNTER
/// - Increment SORRY_COUNTER instead, because this is still a synthetic proof hole
#[test]
#[serial]
fn test_create_trusted_ay_term_fallback_to_smt_proof_stub() {
    // Use Environment::default() (bare struct) instead of Environment::new()
    // because new() now initializes trustedAy by default (since W1-1275).
    let env = Environment::default();

    // Reset counters for isolation
    reset_ay_counter();
    reset_sorry_counter();

    let goal_ty = Expr::prop();

    // Create term - should fall back to the current typed stub lane.
    let term = smt::create_trusted_ay_term(&env, &goal_ty);
    assert!(
        matches!(term.kind(), ExprKind::App(func, arg)
            if matches!(func.kind(), ExprKind::Const(name, _) if name.to_string() == "SMT_PROOF")
                && matches!(arg.kind(), ExprKind::Sort(_))),
        "trustedAy fallback should emit @SMT_PROOF goal_ty, got {term:?}"
    );

    // Ay counter should NOT increment (fell back to sorry)
    assert_eq!(ay_proof_count(), 0, "Ay counter should NOT increment");

    // Sorry counter SHOULD increment (fallback was used)
    assert_eq!(
        sorry_count(),
        1,
        "Sorry counter should increment for fallback"
    );
}

/// Test 5: Counter isolation between tests
///
/// Verify that reset_ay_counter() properly resets the counter.
#[test]
#[serial]
fn test_ay_counter_isolation() {
    let mut env = Environment::new();
    env.init_trusted_ay().unwrap();

    // Create some terms — each call should produce a valid Expr
    let goal_ty = Expr::prop();
    let term1 = smt::create_trusted_ay_term(&env, &goal_ty);
    let term2 = smt::create_trusted_ay_term(&env, &goal_ty);
    // Terms should be non-trivial (App of trustedAy to goal, or the SMT_PROOF stub)
    assert!(
        !matches!(term1.kind(), ExprKind::BVar(..)),
        "ay term should not be a bound variable, got {:?}",
        term1.kind()
    );
    assert!(
        !matches!(term2.kind(), ExprKind::BVar(..)),
        "ay term should not be a bound variable, got {:?}",
        term2.kind()
    );

    // Reset counter
    reset_ay_counter();

    // Counter should be zero
    assert_eq!(ay_proof_count(), 0, "Counter should be 0 after reset");

    // Create one more term
    let term3 = smt::create_trusted_ay_term(&env, &goal_ty);
    assert!(
        !matches!(term3.kind(), ExprKind::BVar(..)),
        "ay term should not be a bound variable after reset, got {:?}",
        term3.kind()
    );
    assert_eq!(ay_proof_count(), 1, "Counter should be 1 after one term");
}

/// Test 6: trustedAy term type checks correctly
///
/// Verify that the produced term has the expected type via the type checker.
#[test]
#[serial]
fn test_trusted_ay_term_type_checks() {
    let mut env = Environment::new();
    env.init_trusted_ay().unwrap();
    env.init_true_false().unwrap(); // Add True type for a concrete Prop

    // Get a concrete proposition type (True is a Prop)
    let goal_ty = Expr::const_(Name::from_string("True"), vec![]);
    let term = smt::create_trusted_ay_term(&env, &goal_ty);

    // Type check the term
    let tc = TypeChecker::new(&env);
    let inferred_ty = tc.infer_type(&term);

    // The inferred type should be True (our goal_ty)
    assert!(
        inferred_ty.is_ok(),
        "trustedAy term should type check: {:?}",
        inferred_ty.err()
    );
    let inferred = inferred_ty.unwrap();

    // Check that the inferred type matches our goal
    if let ExprKind::Const(name, _) = inferred.kind() {
        assert_eq!(name.to_string(), "True", "Inferred type should be True");
    } else {
        panic!("Inferred type should be Const True, got {:?}", inferred);
    }
}
