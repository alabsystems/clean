// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for replace_target_def_eq and replace_target_eq primitives.
//!
//! These tests guard the MetaId(0) connection invariant described in
//! `crates/clean-elab/src/tactic/core/mod.rs:381-421`. When a tactic
//! replaces the current goal's target, the old metavariable must be
//! assigned so that `proof_term()` (which reads MetaId(0)'s assignment)
//! can trace through the chain to the final proof.
//!
//! Part of #2477.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn add_type_family_p(env: &mut Environment) -> Expr {
    add_axiom(
        env,
        "P",
        Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::type_(),
        ),
    );
    Expr::const_(Name::from_string("P"), vec![])
}

fn make_reducible_clean_goal(p: &Expr) -> (Expr, Expr) {
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let reducible_h1_ty = Expr::let_named(
        Name::from_string("h1_alias"),
        Expr::type_(),
        a_ty.clone(),
        Expr::bvar(0),
        false,
    );
    let reducible_h2_ty = Expr::let_named(
        Name::from_string("family_alias"),
        Expr::pi(BinderInfo::Default, a_ty.clone(), Expr::type_()),
        Expr::lam(
            BinderInfo::Default,
            a_ty.clone(),
            Expr::app(p.clone(), Expr::bvar(0)),
        ),
        Expr::app(Expr::bvar(0), Expr::bvar(1)),
        false,
    );
    let reducible_goal_ty = Expr::let_named(
        Name::from_string("target_alias"),
        Expr::type_(),
        b_ty,
        Expr::bvar(0),
        false,
    );
    (
        a_ty,
        Expr::pi(
            BinderInfo::Default,
            reducible_h1_ty,
            Expr::pi(
                BinderInfo::Default,
                reducible_h2_ty,
                Expr::pi(
                    BinderInfo::Default,
                    reducible_goal_ty.clone(),
                    reducible_goal_ty,
                ),
            ),
        ),
    )
}

// =============================================================================
// replace_target_def_eq tests
// =============================================================================

/// Test: replace_target_def_eq preserves proof_term() connection.
///
/// Creates a definition `MyProp := P` (where P : Prop), sets goal to `MyProp`,
/// uses `change` (which delegates to replace_target_def_eq) to switch to `P`,
/// closes the goal with a proof of `P`, and verifies proof extraction works.
#[test]
fn test_replace_target_def_eq_proof_chain() {
    let mut env = Environment::new();

    // P : Prop (axiom)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // MyProp : Prop := P (reducible definition, def-eq to P)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyProp"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // hp : P (proof witness)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    // Goal: MyProp (which is def-eq to P)
    let my_prop = Expr::const_(Name::from_string("MyProp"), vec![]);
    let mut state = ProofState::new(env, my_prop);

    // Use change to replace target with P (exercises replace_target_def_eq)
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let change_result = change(&mut state, p);
    assert!(
        change_result.is_ok(),
        "change should succeed: MyProp is def-eq to P, got: {:?}",
        change_result
    );

    // The goal should now be P
    assert_eq!(state.goals().len(), 1, "should have exactly one goal");
    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::const_(Name::from_string("P"), vec![]),
        "goal target should be P after change"
    );

    // Close the goal with hp : P
    let hp = Expr::const_(Name::from_string("hp"), vec![]);
    let close_result = assumption(&mut state);
    // assumption won't find hp in the context, so use exact
    if close_result.is_err() {
        let exact_result = exact(&mut state, hp);
        assert!(
            exact_result.is_ok(),
            "exact hp should close the P goal, got: {:?}",
            exact_result
        );
    }

    assert!(state.is_complete(), "proof should be complete");

    // KEY ASSERTION: proof_term() must return Some because MetaId(0)
    // is connected through the replace_target_def_eq chain.
    assert!(
        state.proof_term().is_some(),
        "proof_term() must be Some — MetaId(0) chain must not be broken by replace_target_def_eq"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must be Some — proof chain must be extractable"
    );
}

/// Test: replace_target_def_eq rejects non-def-eq targets.
#[test]
fn test_replace_target_def_eq_rejects_non_def_eq() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, p);

    // change to Q should fail — P and Q are not def-eq
    let result = change(&mut state, q);
    assert!(result.is_err(), "change should reject non-def-eq target");
}

/// Test: replace_target_def_eq is a no-op when target is syntactically identical.
#[test]
fn test_replace_target_def_eq_syntactic_noop() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, p.clone());

    let original_meta_id = state.current_goal().unwrap().meta_id;

    // change to the same type should be a no-op
    let result = change(&mut state, p);
    assert!(result.is_ok(), "change to same type should succeed");

    // Meta ID should be unchanged (syntactic shortcut)
    assert_eq!(
        state.current_goal().unwrap().meta_id,
        original_meta_id,
        "syntactically identical change should not allocate a new meta"
    );
}

// =============================================================================
// Unfold proof extraction regression test
// =============================================================================

/// Test: unfold via replace_target_def_eq preserves proof chain (#2477).
///
/// This is the regression test for the bug where apply_unfold_rule
/// replaced state.goals[0] in-place, disconnecting MetaId(0) from
/// the proof chain. After the migration to replace_target_def_eq,
/// unfolding should preserve proof_term() connectivity.
///
/// Setup: MyPred : Prop := P, goal is MyPred, unfold to P via
/// replace_target_def_eq, close with hp : P.
/// Key assertion: proof_term() and closed_proof() are both Some.
#[test]
fn test_unfold_replace_target_proof_extraction() {
    let mut env = Environment::new();

    // P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // MyPred : Prop := P (reducible definition, def-eq to P)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyPred"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // hp : P
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    // Goal: MyPred
    let my_pred = Expr::const_(Name::from_string("MyPred"), vec![]);
    let mut state = ProofState::new(env, my_pred);

    // Simulate unfold: replace MyPred with its body P via replace_target_def_eq.
    // This is exactly what apply_unfold_rule now does internally.
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let replace_result = state.replace_target_def_eq(p.clone());
    assert!(
        replace_result.is_ok(),
        "replace_target_def_eq should succeed: MyPred is def-eq to P, got: {:?}",
        replace_result
    );

    // Goal should now be P
    assert_eq!(state.goals().len(), 1);
    assert_eq!(state.current_goal().unwrap().target, p);

    // Close the goal with hp : P
    let hp = Expr::const_(Name::from_string("hp"), vec![]);
    let close_result = exact(&mut state, hp);
    assert!(
        close_result.is_ok(),
        "exact hp should close P goal, got: {:?}",
        close_result
    );

    assert!(state.is_complete(), "proof should be complete");

    // KEY ASSERTIONS: MetaId(0) chain must be connected.
    // Before #2477, the old pattern (goals[0] = new_goal) left MetaId(0)
    // unassigned, so proof_term() returned None even when goals were empty.
    assert!(
        state.proof_term().is_some(),
        "proof_term() must be Some — MetaId(0) chain must not be broken by unfold"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must be Some — proof must be extractable after unfold"
    );
}

/// Test: multiple chained replace_target_def_eq calls preserve proof chain.
///
/// Chains two unfoldings: MyOuter → MyInner → P, verifying that the
/// MetaId(0) connection is maintained through multiple replacements.
#[test]
fn test_chained_replace_target_def_eq_proof_chain() {
    let mut env = Environment::new();

    // P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // MyInner : Prop := P
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyInner"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // MyOuter : Prop := MyInner
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyOuter"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("MyInner"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // hp : P
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    // Goal: MyOuter
    let my_outer = Expr::const_(Name::from_string("MyOuter"), vec![]);
    let mut state = ProofState::new(env, my_outer);

    // First unfold: MyOuter → MyInner
    let my_inner = Expr::const_(Name::from_string("MyInner"), vec![]);
    assert!(state.replace_target_def_eq(my_inner).is_ok());

    // Second unfold: MyInner → P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    assert!(state.replace_target_def_eq(p).is_ok());

    // Close with hp : P
    let hp = Expr::const_(Name::from_string("hp"), vec![]);
    assert!(exact(&mut state, hp).is_ok());
    assert!(state.is_complete());

    // Proof chain must survive two levels of replacement
    assert!(
        state.proof_term().is_some(),
        "proof_term() must survive chained replace_target_def_eq"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must survive chained replace_target_def_eq"
    );
}

/// Test: delta via replace_target_def_eq preserves proof extraction.
#[test]
fn test_delta_replace_target_proof_extraction() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyInner"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyOuter"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("MyInner"), vec![]),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("MyOuter"), vec![]));
    delta(&mut state).expect("delta should unfold reducible definitions");
    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::const_(Name::from_string("P"), vec![]),
        "delta should expose the base proposition"
    );

    exact(&mut state, Expr::const_(Name::from_string("hp"), vec![]))
        .expect("exact hp should close the delta-reduced goal");
    assert!(state.is_complete(), "delta proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "delta must keep MetaId(0) connected"
    );
    assert!(
        state.closed_proof().is_some(),
        "delta must preserve closed proof extraction"
    );
}

/// Test: dsimp beta/zeta reductions preserve proof extraction.
#[test]
fn test_dsimp_replace_target_beta_zeta_proof_extraction() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let let_expr = Expr::let_named(
        Name::from_string("y"),
        nat.clone(),
        zero.clone(),
        Expr::bvar(0),
        false,
    );
    let reducible = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        let_expr,
    );
    let expected_target = make_equality_type(&nat, &zero, &zero, Level::succ(Level::zero()));
    let goal_target = make_equality_type(&nat, &reducible, &zero, Level::succ(Level::zero()));

    let mut state = ProofState::new(env, goal_target);
    dsimp(&mut state).expect("dsimp should beta/zeta-reduce the target");
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_target,
        "dsimp should reduce the goal to a reflexive equality"
    );

    rfl(&mut state).expect("rfl should close the dsimp-reduced goal");
    assert!(state.is_complete(), "dsimp proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "dsimp must keep MetaId(0) connected"
    );
    assert!(
        state.closed_proof().is_some(),
        "dsimp must preserve closed proof extraction"
    );
}

/// Test: dsimp eta reduction preserves proof extraction.
#[test]
fn test_dsimp_replace_target_eta_proof_extraction() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let fun_ty = Expr::arrow(nat.clone(), nat.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: fun_ty.clone(),
    })
    .unwrap();

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let eta_redex = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(f.clone(), Expr::bvar(0)),
    );
    let expected_target = make_equality_type(&fun_ty, &f, &f, Level::succ(Level::zero()));
    let goal_target = make_equality_type(&fun_ty, &eta_redex, &f, Level::succ(Level::zero()));

    let mut state = ProofState::new(env, goal_target);
    dsimp(&mut state).expect("dsimp should eta-reduce the target");
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_target,
        "dsimp should reduce eta-equivalent functions to a reflexive equality"
    );

    rfl(&mut state).expect("rfl should close the eta-reduced goal");
    assert!(
        state.is_complete(),
        "eta-reduced dsimp proof should be complete"
    );
    assert!(
        state.proof_term().is_some(),
        "eta dsimp must keep MetaId(0) connected"
    );
    assert!(
        state.closed_proof().is_some(),
        "eta dsimp must preserve closed proof extraction"
    );
}

/// Test: clean via replace_target_def_eq preserves proof extraction.
#[test]
fn test_clean_replace_target_proof_extraction() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let reducible = Expr::let_named(
        Name::from_string("y"),
        nat.clone(),
        zero.clone(),
        Expr::bvar(0),
        false,
    );
    let expected_target = make_equality_type(&nat, &zero, &zero, Level::succ(Level::zero()));
    let goal_target = make_equality_type(&nat, &reducible, &zero, Level::succ(Level::zero()));

    let mut state = ProofState::new(env, goal_target);
    clean(&mut state).expect("clean should beta-reduce let expressions in the target");
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_target,
        "clean should reduce the goal to a reflexive equality"
    );

    rfl(&mut state).expect("rfl should close the clean-reduced goal");
    assert!(state.is_complete(), "clean proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "clean must keep MetaId(0) connected"
    );
    assert!(
        state.closed_proof().is_some(),
        "clean must preserve closed proof extraction"
    );
}

/// Test: clean preserves proof extraction when it also mutates hypothesis types.
///
/// This covers the mixed path from #2477 and #2569: the target is rewritten via
/// `replace_target_def_eq`, then dependent local hypothesis types are rewritten
/// through the checked local-ops boundary. The resulting context must still
/// support `assumption`, and the root proof chain through `MetaId(0)` must
/// remain extractable.
#[test]
fn test_clean_replace_target_and_hyp_simplification_still_closes_by_assumption() {
    let mut env = setup_env();
    let p = add_type_family_p(&mut env);
    let (a_ty, theorem_type) = make_reducible_clean_goal(&p);
    let mut state = ProofState::new(env, theorem_type);
    intro(&mut state, "h1").expect("intro should expose the first reducible hypothesis");
    intro(&mut state, "h2").expect("intro should expose the dependent reducible hypothesis");
    intro(&mut state, "h_target").expect("intro should expose the reducible closing hypothesis");
    clean(&mut state).expect("clean should reduce target and local hypothesis types");

    let cleaned_goal = state.current_goal().expect("clean should leave one goal");
    let h1_fvar = cleaned_goal.local_ctx[0].fvar;
    assert_eq!(
        cleaned_goal.local_ctx[0].ty, a_ty,
        "clean should beta-reduce the first hypothesis type to A"
    );
    assert_eq!(
        cleaned_goal.local_ctx[1].ty,
        Expr::app(p.clone(), Expr::fvar(h1_fvar)),
        "clean should beta-reduce the dependent hypothesis using the fresh h1 fvar"
    );
    assert_eq!(
        cleaned_goal.local_ctx[2].ty,
        Expr::const_(Name::from_string("B"), vec![]),
        "clean should beta-reduce the closing hypothesis type to B"
    );
    assert_eq!(
        cleaned_goal.target,
        Expr::const_(Name::from_string("B"), vec![]),
        "clean should beta-reduce the target to B"
    );

    assumption(&mut state).expect("assumption should use the cleaned closing hypothesis");
    assert!(
        state.is_complete(),
        "clean + assumption proof should complete"
    );
    assert!(
        state.proof_term().is_some(),
        "clean must keep MetaId(0) connected even when hypothesis types mutate"
    );
    assert!(
        state.closed_proof().is_some(),
        "clean must preserve closed proof extraction after hypothesis cleanup"
    );
}

// =============================================================================
// replace_target_eq tests
// =============================================================================

/// Test: replace_target_eq builds Eq.mpr proof and preserves chain.
///
/// Goal `@Eq N x y`, identity equality proof via Eq.refl at Prop level,
/// close with `exact hxy`, verify proof_term() is Some.
#[test]
fn test_replace_target_eq_proof_chain() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // N : Type, x y : N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    for name in ["x", "y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("N"), vec![]),
        })
        .unwrap();
    }

    // Build @Eq.{1} N x y
    let n = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let eq_level = Level::succ(Level::zero());
    let eq_n_x_y = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![eq_level.clone()]),
                n.clone(),
            ),
            x.clone(),
        ),
        y.clone(),
    );

    // hxy : @Eq N x y
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hxy"),
        level_params: vec![],
        type_: eq_n_x_y.clone(),
    })
    .unwrap();

    let mut state = ProofState::new(env, eq_n_x_y.clone());

    // eq_proof : (@Eq N x y) = (@Eq N x y) via @Eq.refl.{1} Prop (@Eq.{1} N x y)
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let eq_proof = Expr::app(Expr::app(eq_refl, Expr::prop()), eq_n_x_y.clone());

    let result = state.replace_target_eq(eq_n_x_y.clone(), eq_proof);
    assert!(
        result.is_ok(),
        "replace_target_eq should succeed, got: {:?}",
        result
    );
    assert_eq!(state.goals().len(), 1);

    // Close with hxy, verify proof chain through Eq.mpr
    let hxy = Expr::const_(Name::from_string("hxy"), vec![]);
    assert!(
        exact(&mut state, hxy).is_ok(),
        "exact hxy should close goal"
    );
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "proof_term() must be Some after replace_target_eq"
    );
}

/// Test: trusted fallback preserves proof extraction on non-defeq target rewrites.
#[test]
#[serial]
fn test_replace_target_with_trusted_fallback_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(&mut env, "hq", prop_q.clone());

    let mut state = ProofState::new(env, prop_p);

    state
        .replace_target_with_trusted_fallback(prop_q.clone(), "simp")
        .expect("shared replace-target fallback should rewrite P to Q");
    assert_eq!(
        state.trusted_axiom_count(),
        1,
        "trusted fallback should record exactly one trusted axiom use"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_q,
        "fallback should leave the rewritten target active"
    );

    exact(&mut state, Expr::const_(Name::from_string("hq"), vec![]))
        .expect("exact hq should close the rewritten goal");
    assert!(state.is_complete(), "proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "proof_term() must stay connected through the trusted fallback"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must stay extractable through the trusted fallback"
    );
}

/// Test: missing Eq is reported explicitly and does not mutate the target in place.
#[test]
#[serial]
fn test_replace_target_with_trusted_fallback_requires_eq_environment() {
    let mut env = Environment::new();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let mut state = ProofState::new(env, prop_p.clone());

    let result = state.replace_target_with_trusted_fallback(prop_q, "simp");
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "Eq"),
        "expected explicit EnvironmentMissing(Eq), got: {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "missing Eq must not mutate the goal target in place"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed environment checks must not record a trusted fallback"
    );
}

/// Test: missing Eq.mpr is reported explicitly and does not record trusted fallback usage.
#[test]
#[serial]
fn test_replace_target_with_trusted_fallback_requires_eq_mpr_without_counting_trust() {
    reset_all_counters();

    let mut env = Environment::new();
    env.init_trusted_arith().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(&mut env, "Eq", Expr::type_());

    let mut state = ProofState::new(env, prop_p.clone());
    let axiom_before = axiom_snapshot();

    let result = state.replace_target_with_trusted_fallback(prop_q, "simp");
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "Eq.mpr"),
        "expected explicit EnvironmentMissing(Eq.mpr), got: {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "missing Eq.mpr must not mutate the goal target in place"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed Eq.mpr preconditions must not record trusted fallback usage"
    );
    assert_no_trusted_axiom_usage(
        "replace_target_with_trusted_fallback",
        "missing Eq.mpr preconditions",
        axiom_before,
    );
}

/// Test: proof/type-check failures propagate without recording a trusted fallback.
#[test]
#[serial]
fn test_replace_target_with_trusted_fallback_does_not_count_failed_replacement() {
    reset_all_counters();

    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());

    let mut state = ProofState::new(env, prop_p.clone());
    let axiom_before = axiom_snapshot();

    let result = state.replace_target_with_trusted_fallback(Expr::type_(), "simp");
    // Closed in Wave 88: the trusted fallback must reject Prop -> Type
    // rewrites with a structured TypeMismatch / TypeCheckFailed error,
    // rather than silently constructing a sort-mismatched Eq term.
    assert!(
        matches!(
            result,
            Err(TacticError::TypeCheckFailed(_)) | Err(TacticError::TypeMismatch { .. })
        ),
        "Prop -> Type trusted fallback must fail-closed with a structured error, got {result:?}",
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "failed replacement proof construction must leave the original goal target intact"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed replacement proof construction must not record trusted fallback usage"
    );
    assert_no_trusted_axiom_usage(
        "replace_target_with_trusted_fallback",
        "failed replacement proof construction",
        axiom_before,
    );
}

/// Negative guard for the Wave-88 sort-check: when both targets are
/// `Prop`-sorted the sort check MUST NOT fire, and the trusted fallback
/// must reach its existing `replace_target_eq` path.
#[test]
#[serial]
fn test_replace_target_with_trusted_fallback_prop_to_prop_not_sort_rejected() {
    reset_all_counters();

    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let mut state = ProofState::new(env, prop_p.clone());

    let result = state.replace_target_with_trusted_fallback(prop_q.clone(), "simp");
    // The sort check must not reject Prop -> Prop. If the call still
    // returns an error, it must NOT be a TypeMismatch produced by the
    // sort check (it could be a downstream proof-construction failure,
    // but the sort gate itself must be transparent here).
    if let Err(TacticError::TypeMismatch { expected, actual }) = &result {
        assert!(
            !(expected.contains("sort") && actual.contains("sort")),
            "sort check must not fire on Prop -> Prop rewrites: expected={expected}, actual={actual}",
        );
    }
}

// =============================================================================
// Source ratchet: prevent new in-place target mutations in production code
// =============================================================================

/// Ratchet: in-place `.target = ` mutations in production tactic code.
///
/// After #2477, all goal target replacements should go through
/// `replace_target_def_eq` or `replace_target_eq`. This test scans
/// production tactic source files (excluding tests/) for in-place
/// target assignment patterns and asserts the count matches the known
/// baseline of allowed sites.
///
/// Allowed sites (7 total):
///   - `builtins.rs` conv_nav: temporary sub-state focus (not final target)
///   - `builtins_phase3d_rewrite.rs` conv_focus_rewrite ×2: focus-only conv-body
///     structural replacement (single-focus witness path + multi-focus congr
///     tree path); the outer conv wrapper still owns proof lifting
///   - `core/local_ops.rs` replace_local_decl_with_value_when_possible:
///     validated explicit-value insertion commits the rewritten goal in place
///   - `conv_ext.rs` ×3 (#2477 Phase 4 multi-focus congr): focus NARROWING in
///     the conv sub-ProofState — `conv_congr` defaults the cursor to the last
///     argument, `open_nested_congr` descends into a nested focus, and
///     `conv_congr_select` selects a sibling sub-focus. SOUNDNESS: these set the
///     sub-goal target to a *sub-expression focus* only; the proof of the whole
///     equality is carried by the `conv_focus_tree` per-focus equalities and is
///     recombined + KERNEL-CHECKED via `replace_target_eq` at the conv
///     reconstruction boundary (`eval_conv_goal` / `eval_conv`). The narrowing
///     never commits a final proof-bearing target — identical category to the
///     pre-existing `builtins.rs conv_nav` focus.
///
/// If this test fails because the count increased, you must migrate the
/// new site to use `replace_target_def_eq` or `replace_target_eq`.
/// If the count decreased, lower the baseline to lock in the improvement.
#[test]
fn test_ratchet_no_new_inplace_target_mutations() {
    let tactic_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tactic");

    let mut violations = Vec::new();
    let mut total_count = 0u32;

    scan_dir_for_target_mutations(&tactic_dir, &tactic_dir, &mut violations, &mut total_count);

    // Known baseline: 6 allowed in-place target mutations in production code.
    // builtins.rs:  g.target = conv.focus;         (conv_nav temporary state)
    // builtins_phase3d_rewrite.rs ×2: g.target = new_target; (conv focus rewrite:
    //   single-focus witness path + multi-focus congr-tree path)
    // conv_ext.rs ×3: g.target = working;          (#2477 Phase 4 multi-focus
    //   congr focus narrowing — proof carried by conv_focus_tree + kernel-checked
    //   at the reconstruction boundary; see the doc comment above for SOUNDNESS).
    const BASELINE: u32 = 6;

    assert!(
        total_count <= BASELINE,
        "In-place `.target = ` mutation count increased from {BASELINE} to {total_count}.\n\
         New sites must use replace_target_def_eq or replace_target_eq instead.\n\
         Violations:\n{}",
        violations
            .iter()
            .map(|(f, l, s)| format!("  {f}:{l}: {s}"))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // Lock in improvements: if count decreased, update the baseline constant.
    if total_count < BASELINE {
        panic!(
            "In-place `.target = ` count decreased from {BASELINE} to {total_count} — \
             update BASELINE in test_ratchet_no_new_inplace_target_mutations to {total_count} \
             to lock in the improvement."
        );
    }
}

/// Recursively scan directory for `.target = ` assignments in non-test .rs files.
fn scan_dir_for_target_mutations(
    root: &std::path::Path,
    dir: &std::path::Path,
    violations: &mut Vec<(String, usize, String)>,
    count: &mut u32,
) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            // Skip test directories
            if path.file_name().is_some_and(|n| n == "tests") {
                continue;
            }
            scan_dir_for_target_mutations(root, &path, violations, count);
        } else if path.extension().is_some_and(|e| e == "rs") {
            let Ok(content) = std::fs::read_to_string(&path) else {
                continue;
            };
            let rel_path = path.strip_prefix(root).unwrap_or(&path);
            for (line_num, line) in content.lines().enumerate() {
                let trimmed = line.trim();
                // Skip comments and doc comments
                if trimmed.starts_with("//") || trimmed.starts_with("///") {
                    continue;
                }
                // Match `.target = ` but not `.target == ` (comparison)
                if let Some(pos) = trimmed.find(".target") {
                    let after_target = &trimmed[pos + 7..];
                    let after_ws = after_target.trim_start();
                    if after_ws.starts_with("= ") && !after_ws.starts_with("== ") {
                        *count += 1;
                        violations.push((
                            rel_path.display().to_string(),
                            line_num + 1,
                            trimmed.to_string(),
                        ));
                    }
                }
            }
        }
    }
}
