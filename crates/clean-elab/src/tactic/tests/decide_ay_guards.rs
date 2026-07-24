// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zero-trust guards: decide() must not produce trustedAy terms.
//!
//! Part of #2442 Phase 3: guards against trustedAy regression on propositional
//! and equality goals that go through the SMT bridge. Uses `with_prelude()`
//! (which includes `init_trusted_ay()`) so that the trustedAy axiom is
//! available — making these tests sensitive to fallback regressions.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

/// Guard: `decide()` must not produce trustedAy for a `True` goal.
///
/// This was the historically suspected remaining trustedAy baseline producer:
/// the SMT bridge could not translate `True` and returned Unverified, causing
/// the old shared recovery helper to synthesize a whole-goal `trustedAy` term.
///
/// After Phase 2D improvements, `True` should be handled without trusted axioms
/// (either by the bridge or by superposition finding `True.intro`). After
/// `#2659`, the shared recovery lane also fails closed instead of reviving the
/// removed whole-goal fallback.
#[test]
#[serial]
fn test_decide_true_goal_no_trusted_ay_with_prelude() {
    reset_all_counters();
    let env = Environment::with_prelude();
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, true_const);

    let result = decide(&mut state);
    let ay_used = ay_proof_count();

    // decide may fail on non-equality goals (returns SmtFailed), but if it
    // succeeds it must not use trustedAy.
    if result.is_ok() {
        assert_eq!(
            state.trusted_axiom_count(),
            0,
            "decide proved True but used {} trusted axioms (expected 0)",
            state.trusted_axiom_count()
        );
        assert_eq!(
            ay_used, 0,
            "decide proved True but produced {} trustedAy terms (expected 0)",
            ay_used
        );
    }
    // If decide fails on True, that's acceptable — True is not an equality
    // goal and the bridge may not support it. But it must not produce trustedAy
    // on the failure path (failure returns Err, not a trusted proof).
    assert_eq!(
        ay_used, 0,
        "decide must not produce trustedAy terms on True goal (got {})",
        ay_used
    );
}

/// Guard: `decide()` must not produce trustedAy for an equality goal
/// when `with_prelude()` provides trustedAy in the environment.
///
/// This is the positive-path counterpart: reflexive equality should go
/// through kernel proof reconstruction, never touching trustedAy.
/// Uses `0 = 0` (Nat literals) since they have stable universe levels.
#[test]
#[serial]
fn test_decide_eq_reflexivity_no_trusted_ay_with_prelude() {
    reset_all_counters();
    let env = Environment::with_prelude();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::nat_lit(0);
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            zero.clone(),
        ),
        zero,
    );

    let mut state = ProofState::new(env, target);
    decide(&mut state).expect("decide should prove 0 = 0");

    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "decide reflexivity must not use trusted axioms (used {})",
        state.trusted_axiom_count()
    );
    assert_eq!(
        ay_proof_count(),
        0,
        "decide reflexivity must not produce trustedAy (produced {})",
        ay_proof_count()
    );
}

fn unsupported_prop_goal_state() -> (ProofState, Goal, Expr) {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add unsupported atomic proposition");
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("goal").clone();
    (state, goal, target)
}

#[test]
#[serial]
fn test_superposition_or_fail_closed_fails_closed_without_trusted_ay() {
    reset_all_counters();
    let (mut state, goal, target) = unsupported_prop_goal_state();
    let ay_before = ay_proof_count();

    let result = smt::superposition_or_fail_closed_for_test(&mut state, &goal, &target);

    assert!(
        matches!(
            result,
            Err(TacticError::SmtFailed { ref tactic, ref detail })
                if tactic == "decide"
                    && detail.contains("reconstruction failed for atom (P)")
        ),
        "whole-goal fallback should now fail closed with target diagnostics, got: {result:?}"
    );
    assert_eq!(
        ay_proof_count() - ay_before,
        0,
        "fail-closed shared recovery must not synthesize trustedAy"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "fail-closed shared recovery must not record trusted axioms"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after fail-closed shared recovery"
    );
}
