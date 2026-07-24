// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof-producing `reduce_eq` tactic and `prove_eq_by_reduction`.
//!
//! These tests verify that the elaborator-level WHNF proof generation
//! correctly produces explicit proof terms for computational equality.
//!
//! Part of #685.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;

/// Environment with Nat, Eq, and a reducible definition `myZero := Nat.zero`.
fn setup_env_with_def() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // myZero : Nat := Nat.zero (reducible, so delta-unfolds)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myZero"),
        level_params: vec![],
        type_: nat.clone(),
        value: zero.clone(),
        is_reducible: true,
    })
    .unwrap();

    // myZero2 : Nat := Nat.zero (another alias, for both-sides-reduce test)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myZero2"),
        level_params: vec![],
        type_: nat,
        value: zero,
        is_reducible: true,
    })
    .unwrap();

    env
}

/// Helper: build `@Eq.{1} Nat lhs rhs`
fn nat_eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs,
        ),
        rhs,
    )
}

// =========================================================================
// reduce_eq tactic tests
// =========================================================================

#[test]
fn test_reduce_eq_reflexive() {
    // Goal: Nat.zero = Nat.zero (trivial, both sides identical)
    let env = setup_env_with_def();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(zero.clone(), zero);

    let mut state = ProofState::new(env, goal);
    reduce_eq(&mut state).expect("reduce_eq should close a = a");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_reduce_eq_delta_one_side() {
    // Goal: myZero = Nat.zero
    // myZero delta-unfolds to Nat.zero, so lhs reduces to rhs
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    reduce_eq(&mut state).expect("reduce_eq should close myZero = Nat.zero");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_reduce_eq_delta_both_sides() {
    // Goal: myZero = myZero2
    // Both sides delta-unfold to Nat.zero
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let my_zero2 = Expr::const_(Name::from_string("myZero2"), vec![]);
    let goal = nat_eq_goal(my_zero, my_zero2);

    let mut state = ProofState::new(env, goal);
    reduce_eq(&mut state).expect("reduce_eq should close myZero = myZero2");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_reduce_eq_delta_rhs_only() {
    // Goal: Nat.zero = myZero
    // Only rhs needs delta reduction (symmetry case)
    let env = setup_env_with_def();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let goal = nat_eq_goal(zero, my_zero);

    let mut state = ProofState::new(env, goal);
    reduce_eq(&mut state).expect("reduce_eq should close Nat.zero = myZero");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_reduce_eq_fails_non_equality() {
    // Goal: Nat (not an equality)
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut state = ProofState::new(env, nat);
    let result = reduce_eq(&mut state);
    assert!(
        result.is_err(),
        "reduce_eq should fail on non-equality goal"
    );
}

#[test]
fn test_reduce_eq_fails_distinct_values() {
    // Goal: Nat.zero = Nat.succ Nat.zero
    // These don't reduce to the same form
    let env = setup_env_with_def();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let goal = nat_eq_goal(zero, one);

    let mut state = ProofState::new(env, goal);
    let result = reduce_eq(&mut state);
    assert!(result.is_err(), "reduce_eq should fail on 0 = 1");
}

// =========================================================================
// prove_eq_by_reduction direct tests
// =========================================================================

#[test]
fn test_prove_eq_by_reduction_beta() {
    // Prove: (fun x => x) Nat.zero = Nat.zero
    // LHS beta-reduces to Nat.zero
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // (fun x : Nat => x) applied to Nat.zero
    let id_app = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        zero.clone(),
    );
    let goal_expr = nat_eq_goal(id_app, zero);

    let mut state = ProofState::new(env, goal_expr);
    reduce_eq(&mut state).expect("reduce_eq should close (fun x => x) 0 = 0");
    assert!(state.is_complete());
}

#[test]
fn test_prove_eq_by_reduction_returns_none_for_distinct() {
    // Directly test prove_eq_by_reduction returns None
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let goal_expr = nat_eq_goal(zero.clone(), one.clone());
    let state = ProofState::new(env, goal_expr);

    let goal = state.current_goal().unwrap().clone();
    let u = Level::succ(Level::zero());
    let result = state.prove_eq_by_reduction(&goal, &nat, &zero, &one, u);
    assert!(result.is_none(), "should return None for 0 != 1");
}

// =========================================================================
// rfl → reduce_eq fallback tests (Part of #685)
// =========================================================================

#[test]
fn test_rfl_fallback_delta_one_side() {
    // rfl on `myZero = Nat.zero`: Eq.refl fails (syntactically different),
    // but the reduce_eq fallback should close via delta reduction.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    rfl(&mut state).expect("rfl should close myZero = Nat.zero via reduce_eq fallback");
    assert!(state.is_complete(), "rfl should fully close the goal");
}

#[test]
fn test_rfl_fallback_delta_both_sides() {
    // rfl on `myZero = myZero2`: both sides delta-unfold to Nat.zero.
    // Eq.refl fails; reduce_eq fallback should close it.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let my_zero2 = Expr::const_(Name::from_string("myZero2"), vec![]);
    let goal = nat_eq_goal(my_zero, my_zero2);

    let mut state = ProofState::new(env, goal);
    rfl(&mut state).expect("rfl should close myZero = myZero2 via reduce_eq fallback");
    assert!(state.is_complete());
}

#[test]
fn test_rfl_fallback_beta_reduction() {
    // rfl on `(fun x => x) 0 = 0`: beta-reducible, Eq.refl might not
    // handle it directly; reduce_eq fallback should close.
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_app = Expr::app(
        Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
        zero.clone(),
    );
    let goal = nat_eq_goal(id_app, zero);

    let mut state = ProofState::new(env, goal);
    rfl(&mut state).expect("rfl should close (fun x => x) 0 = 0");
    assert!(state.is_complete());
}

#[test]
fn test_rfl_fallback_fails_distinct() {
    // rfl on `0 = 1` should still fail (reduce_eq can't make them equal either)
    let env = setup_env_with_def();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let goal = nat_eq_goal(zero, one);

    let mut state = ProofState::new(env, goal);
    let result = rfl(&mut state);
    assert!(result.is_err(), "rfl should fail on 0 = 1");
}

// =========================================================================
// aesop integration: equality closed via reduce_eq during search
// =========================================================================

#[test]
fn test_aesop_closes_delta_equality_via_reduce_eq() {
    // Goal: myZero = Nat.zero where myZero := Nat.zero (delta-reducible)
    // Aesop should close this via aesop_try_close -> rfl -> reduce_eq fallback.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    aesop(&mut state).expect("aesop should close delta-equality via rfl->reduce_eq");
    assert!(
        state.goals().is_empty(),
        "aesop should close myZero = Nat.zero via reduce_eq"
    );
}

#[test]
fn test_aesop_closes_beta_equality_via_reduce_eq() {
    // Goal: (fun x => x) Nat.zero = Nat.zero
    // Aesop should close this via rfl -> reduce_eq (beta reduction).
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_fn = Expr::lam(BinderInfo::Default, nat, Expr::bvar(0));
    let beta_app = Expr::app(id_fn, zero.clone());
    let goal = nat_eq_goal(beta_app, zero);

    let mut state = ProofState::new(env, goal);
    aesop(&mut state).expect("aesop should close beta-equality via rfl->reduce_eq");
    assert!(state.goals().is_empty());
}

// =========================================================================
// mathverse/linarith/norm_num integration: reduce_eq pre-step (#685)
// =========================================================================

#[test]
fn test_mathverse_closes_delta_equality_via_reduce_eq() {
    // Goal: myZero = Nat.zero
    // mathverse's reduce_eq pre-step should close this via delta reduction,
    // without needing the full constraint solver pipeline.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    omega(&mut state).expect("mathverse should close myZero = Nat.zero via reduce_eq pre-step");
    assert!(state.is_complete());
}

#[test]
fn test_mathverse_closes_beta_equality_via_reduce_eq() {
    // Goal: (fun x => x) Nat.zero = Nat.zero
    // mathverse's reduce_eq pre-step should close via beta reduction.
    let env = setup_env_with_def();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_fn = Expr::lam(BinderInfo::Default, nat, Expr::bvar(0));
    let beta_app = Expr::app(id_fn, zero.clone());
    let goal = nat_eq_goal(beta_app, zero);

    let mut state = ProofState::new(env, goal);
    omega(&mut state).expect("mathverse should close beta-equality via reduce_eq pre-step");
    assert!(state.is_complete());
}

#[test]
fn test_linarith_closes_delta_equality_via_reduce_eq() {
    // Goal: myZero = Nat.zero
    // linarith's reduce_eq pre-step should close via delta reduction.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    linarith(&mut state).expect("linarith should close myZero = Nat.zero via reduce_eq pre-step");
    assert!(state.is_complete());
}

#[test]
fn test_linarith_closes_both_sides_delta_via_reduce_eq() {
    // Goal: myZero = myZero2
    // Both sides delta-unfold to Nat.zero; linarith should close via reduce_eq.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let my_zero2 = Expr::const_(Name::from_string("myZero2"), vec![]);
    let goal = nat_eq_goal(my_zero, my_zero2);

    let mut state = ProofState::new(env, goal);
    linarith(&mut state).expect("linarith should close myZero = myZero2 via reduce_eq");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_closes_delta_equality_via_reduce_eq() {
    // Goal: myZero = Nat.zero
    // norm_num's reduce_eq fallback should close via delta reduction.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let goal = nat_eq_goal(my_zero, zero);

    let mut state = ProofState::new(env, goal);
    norm_num(&mut state).expect("norm_num should close myZero = Nat.zero via reduce_eq fallback");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_closes_both_sides_delta_via_reduce_eq() {
    // Goal: myZero = myZero2
    // norm_num's reduce_eq fallback should close via delta reduction.
    let env = setup_env_with_def();
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let my_zero2 = Expr::const_(Name::from_string("myZero2"), vec![]);
    let goal = nat_eq_goal(my_zero, my_zero2);

    let mut state = ProofState::new(env, goal);
    norm_num(&mut state).expect("norm_num should close myZero = myZero2 via reduce_eq fallback");
    assert!(state.is_complete());
}
