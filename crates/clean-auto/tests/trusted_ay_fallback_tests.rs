// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Integration tests verifying trustedAy fallback behavior in clean-auto.
// Part of #2051 audit: when SMT proves a goal but proof reconstruction fails,
// the fallback should use trustedAy (not sorry).

use clean_auto::AutomationEngine;
use clean_kernel::sorry::{
    ay_proof_count, create_trusted_ay_term, reset_ay_counter, reset_sorry_counter, sorry_count,
};
use clean_kernel::{env::Declaration, BinderInfo, Environment, Expr, Level, Name};
use serial_test::serial;
use std::time::Duration;

/// Set up a minimal environment with Eq, Eq.refl, and test constants.
/// Uses Environment::default() (no trustedAy) so tests can control axiom presence.
fn setup_env_with_eq() -> Environment {
    let mut env = Environment::default();

    // Add Eq type: Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();

    // Add Eq.refl : ∀ {α : Sort u} (a : α), Eq a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();

    // Add a base type A : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants a, b : A
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    env
}

/// Construct Eq A lhs rhs
fn make_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Verify that auto_prove in an environment with trustedAy never produces sorry.
///
/// Part of #2051 audit: when SMT proves a goal but proof reconstruction fails,
/// the fallback should use trustedAy (increments AY_PROOF_COUNTER), not sorry
/// (increments SORRY_COUNTER). This test verifies the regression guard.
#[test]
#[serial]
fn test_auto_prove_no_sorry_in_trusted_env() {
    // Setup env WITH trustedAy (unlike unit tests that use minimal env)
    let mut env = setup_env_with_eq();
    env.init_trusted_ay().unwrap();

    reset_sorry_counter();
    reset_ay_counter();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let engine = AutomationEngine::new();
    let result = engine.auto_prove(&env, &goal, Duration::from_secs(5), None);

    assert!(result.is_some(), "Should prove reflexive equality");
    assert_eq!(
        sorry_count(),
        0,
        "auto_prove should not produce sorry terms in an environment with trustedAy"
    );
}

/// Verify that create_trusted_ay_term (the fallback used by auto_prove)
/// increments AY_PROOF_COUNTER and NOT SORRY_COUNTER when trustedAy is available.
///
/// This directly tests the fallback path that fires when try_smt_prove returns
/// Some(result) with proof_term: None. Part of #2051 AC1.
#[test]
#[serial]
fn test_trusted_ay_fallback_uses_ay_counter_not_sorry() {
    let mut env = setup_env_with_eq();
    env.init_trusted_ay().unwrap();

    reset_sorry_counter();
    reset_ay_counter();

    let goal = Expr::prop();

    // Directly call the fallback function that auto_prove uses
    let _term = create_trusted_ay_term(&env, &goal);

    assert_eq!(
        ay_proof_count(),
        1,
        "create_trusted_ay_term should increment AY_PROOF_COUNTER"
    );
    assert_eq!(
        sorry_count(),
        0,
        "create_trusted_ay_term should NOT increment SORRY_COUNTER when trustedAy is available"
    );
}

/// Verify that without trustedAy axiom, the fallback degrades to sorry.
/// This documents the current behavior so any future change is intentional.
#[test]
#[serial]
fn test_trusted_ay_fallback_degrades_to_sorry_without_axiom() {
    // Minimal env without trustedAy
    let env = setup_env_with_eq();

    reset_sorry_counter();
    reset_ay_counter();

    let goal = Expr::prop();

    let _term = create_trusted_ay_term(&env, &goal);

    assert_eq!(
        ay_proof_count(),
        0,
        "Without trustedAy axiom, AY_PROOF_COUNTER should not increment"
    );
    assert_eq!(
        sorry_count(),
        1,
        "Without trustedAy axiom, should fall back to sorry"
    );
}
