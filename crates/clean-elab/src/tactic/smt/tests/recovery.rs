// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
#[cfg(feature = "ay-smt")]
use crate::tactic::smt::bridge_reconstruction;
use crate::tactic::{LocalDecl, TacticError};
use clean_kernel::mode::CleanMode;
#[cfg(not(feature = "ay-smt"))]
use serial_test::serial;

// ============================================================================
// Bridge validation support tests (Part of #2442)
// ============================================================================

/// Verify that `init_bridge_validation_support` succeeds on a fully initialized
/// environment. The function must not panic and must leave the environment in a
/// consistent state for kernel validation of bridge-produced arithmetic proofs.
#[test]
fn test_bridge_validation_support_succeeds_on_full_env() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat should initialize");
    env.init_le().expect("LE should initialize");
    env.init_lt().expect("LT should initialize");

    let goal_ty = Expr::prop();
    let mut state = ProofState::new(env, goal_ty);

    // Should not panic; both init_smt_bridge_nat_order_lemmas and
    // init_int_ord_lemmas should succeed on a prelude-initialized env.
    bridge_validation::init_bridge_validation_support(&mut state);

    // After initialization, the environment should contain Nat order lemmas.
    // Verify by checking that a representative constant exists.
    let has_le_trans = state
        .env()
        .get_const(&Name::from_string("Nat.le_trans"))
        .is_some();
    assert!(
        has_le_trans,
        "Nat.le_trans should be available after bridge validation support init"
    );
}

// Note: minimal-env bootstrap and idempotency tests live in
// bridge_validation_support_tests.rs so the oversized smt/tests.rs file only
// carries the shared full-env regression.

// ============================================================================
// Superposition fallback soundness tests (Part of #2442)
// ============================================================================

/// Verify that `try_superposition_fallback` returns `None` for a goal that
/// is not provable from the local context. This is the critical trust boundary:
/// when superposition returns None, the shared recovery lane must fail closed.
///
/// This tests the negative case of the fallback — ensuring the system does
/// NOT claim to prove something it can't.
#[test]
fn test_superposition_fallback_returns_none_for_unprovable_goal() {
    use crate::tactic::smt::try_superposition_fallback;

    let env = Environment::new();
    // Goal: False (unprovable without hypotheses)
    let target = Expr::const_(Name::from_string("False"), vec![]);

    let mut state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("should have a goal").clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_unprovable");
    assert!(
        matches!(result, Ok(None)),
        "superposition should not prove False without hypotheses"
    );
}

/// Verify that `try_superposition_fallback` returns `None` for a goal
/// between unrelated constants (a = b without any hypothesis linking them).
/// This ensures the superposition prover doesn't produce spurious proofs.
#[test]
fn test_superposition_fallback_returns_none_for_unrelated_eq() {
    use crate::tactic::smt::try_superposition_fallback;
    use clean_kernel::level::Level;

    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");

    let a_ty = Expr::type_();
    let a = Expr::const_(Name::from_string("P"), vec![]);
    let b = Expr::const_(Name::from_string("Q"), vec![]);

    // Eq.{1} Type P Q — not provable without hypotheses
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a,
        ),
        b,
    );

    let mut state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("should have a goal").clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_unrelated_eq");
    assert!(
        matches!(result, Ok(None)),
        "superposition should not prove P = Q without linking hypotheses"
    );
}

fn setup_eq_env() -> Environment {
    use clean_kernel::env::Declaration;

    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A should register");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: a_ty.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }
    env
}

fn make_eq(type_: Expr, lhs: Expr, rhs: Expr) -> Expr {
    use clean_kernel::level::Level;

    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                type_,
            ),
            lhs,
        ),
        rhs,
    )
}

fn equality_goal_state_with_sort_local() -> (ProofState, Expr) {
    use clean_kernel::FVarId;

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let target = make_eq(a_ty, a, b);
    let state = ProofState::with_context(
        setup_eq_env(),
        target.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(1),
                name: "T".to_string(),
                ty: Expr::type_(),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h".to_string(),
                ty: target.clone(),
                value: None,
            },
        ],
    );

    (state, target)
}

#[test]
fn test_superposition_fallback_ignores_sort_locals_but_keeps_eq_hypotheses() {
    use crate::tactic::smt::try_superposition_fallback;

    let (mut state, target) = equality_goal_state_with_sort_local();
    let goal = state.current_goal().expect("should have a goal").clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_sort_locals");
    assert!(
        matches!(result, Ok(Some(_))),
        "superposition should use h : a = b while ignoring T : Type"
    );
}

#[test]
fn test_superposition_fallback_returns_bootstrap_error_in_cubical_mode() {
    use crate::tactic::smt::try_superposition_fallback;
    use clean_kernel::env::Declaration;
    use clean_kernel::FVarId;

    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.init_eq().expect("Eq should initialize");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A should register");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: a_ty.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let target = make_eq(a_ty, a, b);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(7),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal").clone();

    let result =
        try_superposition_fallback(&mut state, &goal, &target, "test_cubical_superposition");

    assert!(
        matches!(
            result,
            Err(TacticError::SmtFailed { ref tactic, ref detail })
                if tactic == "test_cubical_superposition"
                    && detail.contains("classical bootstrap failed")
                    && detail.contains("Cubical")
        ),
        "cubical recovery should surface the bootstrap error directly: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open when cubical mode blocks classical recovery"
    );
}

// ============================================================================
// Invalid-candidate validation branch test (Part of #2937)
// ============================================================================

/// Verify that `validate_superposition_candidate` returns `None` when given an
/// ill-typed proof candidate. This exercises the exact branch that was
/// previously hidden by `.ok()` — the candidate is rejected by kernel
/// validation and the helper logs the error before returning `None`.
#[test]
fn test_validate_superposition_candidate_returns_none_for_ill_typed_proof() {
    use crate::tactic::smt::validate_superposition_candidate_for_test;
    use clean_kernel::level::Level;

    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");

    // Build an equality target: Eq.{1} Prop True True
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::prop(),
            ),
            Expr::const_(Name::from_string("True"), vec![]),
        ),
        Expr::const_(Name::from_string("True"), vec![]),
    );

    let state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("should have a goal").clone();

    // Pass Prop itself as a bogus proof term — it is not a proof of True = True.
    let bogus_proof = Expr::prop();
    let result = validate_superposition_candidate_for_test(
        &state,
        &goal,
        &bogus_proof,
        &target,
        "test_invalid_candidate",
    );

    assert!(
        result.is_none(),
        "ill-typed proof candidate should be rejected by kernel validation, got: {result:?}"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_bridge_reconstruction_candidate_ignores_sort_locals_but_keeps_eq_hypotheses() {
    let (mut state, target) = equality_goal_state_with_sort_local();
    let goal = state.current_goal().expect("should have a goal").clone();

    let candidate = bridge_reconstruction::try_bridge_reconstruction_candidate(
        &mut state,
        &goal,
        &target,
        "test_bridge_reconstruction_candidate",
    )
    .into_candidate()
    .expect("bridge reconstruction should use h : a = b while ignoring T : Type");

    assert_eq!(
        candidate.trust_subterm_count, 0,
        "simple assumption recovery should stay zero-trust"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_recover_verified_goal_after_gap_records_invalid_bridge_candidate_on_validation_failed_probe(
) {
    let (mut state, target) = equality_goal_state_with_sort_local();
    let goal = state.current_goal().expect("should have a goal").clone();
    let _guard = bridge_reconstruction::install_test_bridge_probe_outcome(
        bridge_reconstruction::BridgeProbeOutcome::ValidationFailed,
    );

    let result =
        bridge_reconstruction::recover_verified_goal_after_reconstruction_gap_with_requirement(
            &mut state,
            &goal,
            &target,
            "test_bridge_validation_failed",
            bridge_reconstruction::RecoveryTrustRequirement::Any,
        );

    assert!(
        result.is_ok(),
        "superposition fallback should recover after an invalid bridge probe, got: {result:?}"
    );
    assert_eq!(
        state.trust_ledger().smt_recovery.invalid_bridge_candidates,
        1,
        "recovery boundary should record exactly one invalid bridge candidate after probe validation fails"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "superposition recovery after bridge validation failure must not add trustedAy debt"
    );
}

#[cfg(not(feature = "ay-smt"))]
#[test]
#[serial]
fn test_recover_verified_goal_after_reconstruction_gap_preserves_tactic_name() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add unsupported atomic proposition");
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("goal").clone();
    let failures_before = ay_reconstruction_failure_count();

    let result = bridge_reconstruction::recover_verified_goal_after_reconstruction_gap(
        &mut state, &goal, &target, "ay_smt",
    );

    assert!(
        matches!(
            result,
            Err(TacticError::SmtFailed { ref tactic, ref detail })
                if tactic == "ay_smt"
                    && detail.contains("reconstruction failed for atom (P)")
        ),
        "shared recovery helper should preserve the caller tactic name, got: {result:?}"
    );
    assert_eq!(
        ay_reconstruction_failure_count() - failures_before,
        1,
        "shared recovery helper should record exactly one reconstruction miss"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after shared fail-closed recovery"
    );
}

// ============================================================================
// Fallback-target classifier tests (moved from decide.rs inline tests,
// Part of #2791)
// ============================================================================

use super::super::decide::{classify_trusted_ay_fallback_target, trusted_ay_fallback_target_head};
use clean_kernel::BinderInfo;

fn prop_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_classify_trusted_ay_fallback_target_eq() {
    let target = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), Expr::prop()),
            prop_const("P"),
        ),
        prop_const("Q"),
    );

    assert_eq!(classify_trusted_ay_fallback_target(&target), "eq");
    assert_eq!(
        trusted_ay_fallback_target_head(&target).as_deref(),
        Some("Eq")
    );
}

#[test]
fn test_classify_trusted_ay_fallback_target_implies_and_forall() {
    let domain = Expr::prop();
    let implies = Expr::pi(BinderInfo::Default, domain.clone(), Expr::prop());
    let forall = Expr::pi(BinderInfo::Default, domain, Expr::bvar(0));

    assert_eq!(classify_trusted_ay_fallback_target(&implies), "implies");
    assert_eq!(classify_trusted_ay_fallback_target(&forall), "forall");
    assert_eq!(
        trusted_ay_fallback_target_head(&implies).as_deref(),
        Some("Pi")
    );
}

#[test]
fn test_classify_trusted_ay_fallback_target_comparison() {
    let target = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            prop_const("a"),
        ),
        prop_const("b"),
    );

    assert_eq!(classify_trusted_ay_fallback_target(&target), "le");
    assert_eq!(
        trusted_ay_fallback_target_head(&target).as_deref(),
        Some("Nat.le")
    );
}

#[test]
fn test_classify_trusted_ay_fallback_target_atom_without_const_head() {
    use clean_kernel::ExprKind;

    let target = Expr::app(Expr::bvar(0), prop_const("P"));

    assert_eq!(classify_trusted_ay_fallback_target(&target), "atom");
    assert!(
        matches!(target.get_app_fn().kind(), ExprKind::BVar(0)),
        "test fixture should use a non-constant application head"
    );
    assert_eq!(trusted_ay_fallback_target_head(&target), None);
}
