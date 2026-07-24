// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-scope regressions for tactics that introduce facts into a continuation.

use super::*;

fn nat_ge(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::mk_tc_rel(
        Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::const_(Name::from_string("instLENat"), vec![]),
        lhs,
        rhs,
    )
}

fn assert_meta_scope(state: &ProofState, goal: &Goal, expected: &[FVarId]) {
    let meta = state
        .metas()
        .get(goal.meta_id)
        .expect("every tactic goal must have a declared metavariable");
    let actual: Vec<_> = meta.locals.iter().map(|(_, fvar, _)| *fvar).collect();
    assert_eq!(
        actual, expected,
        "metavariable must capture its exact scope"
    );
}

#[test]
fn positivity_at_creates_dependent_obligation_and_kernel_closed_chain() {
    let mut env = setup_env();
    env.init_ge()
        .expect("GE/LE/Nat environment should initialize");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // (x : Nat) -> x >= 0 -> A
    let original_target = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::pi(
            BinderInfo::Default,
            nat_ge(Expr::bvar(0), Expr::nat_lit(0)),
            a_ty.clone(),
        ),
    );
    let mut state = ProofState::new(env.clone(), original_target.clone());
    intro(&mut state, "x").expect("introduce x");
    intro(&mut state, "h").expect("introduce x >= 0");

    let original_ctx = state
        .current_goal()
        .expect("goal remains")
        .local_ctx
        .clone();
    let x_fvar = original_ctx[0].fvar;
    let h_fvar = original_ctx[1].fvar;

    let mut config = PositivityAtConfig::new().with_name("h_pos");
    config.try_stronger = false;
    positivity_at_with_config(&mut state, "h", config)
        .expect("positivity_at should create a proof-carrying continuation");

    assert_eq!(state.goals().len(), 2);
    let lemma_goal = &state.goals()[0];
    let continuation_goal = &state.goals()[1];
    assert_eq!(
        lemma_goal.target,
        nat_ge(Expr::fvar(x_fvar), Expr::nat_lit(0))
    );
    assert_eq!(lemma_goal.local_ctx.len(), 2);
    assert_eq!(continuation_goal.target, a_ty);
    assert_eq!(continuation_goal.local_ctx.len(), 3);
    assert_eq!(continuation_goal.local_ctx[2].name, "h_pos");
    let h_pos_fvar = continuation_goal.local_ctx[2].fvar;
    assert_meta_scope(&state, lemma_goal, &[x_fvar, h_fvar]);
    assert_meta_scope(&state, continuation_goal, &[x_fvar, h_fvar, h_pos_fvar]);

    exact(&mut state, Expr::fvar(h_fvar)).expect("existing comparison proves the obligation");
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![]))
        .expect("close the continuation");

    assert!(state.is_complete());
    let proof = state
        .closed_proof()
        .expect("proof-carrying chain must yield a closed proof");
    TypeChecker::new(&env)
        .check_type(&proof, &original_target)
        .expect("kernel must accept the positivity proof chain");
}

#[test]
fn nontriviality_creates_dependent_obligation_and_kernel_closed_chain() {
    let mut env = setup_env();
    env.init_nontrivial()
        .expect("Nontrivial environment should initialize");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let nontrivial_alpha = Expr::app(
        Expr::const_(Name::from_string("Nontrivial"), vec![Level::zero()]),
        Expr::bvar(0),
    );
    // (alpha : Type) -> Nontrivial alpha -> A
    let original_target = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, nontrivial_alpha, a_ty.clone()),
    );
    let mut state = ProofState::new(env.clone(), original_target.clone());
    intro(&mut state, "alpha").expect("introduce alpha");
    intro(&mut state, "h_alpha").expect("introduce Nontrivial alpha");

    let original_ctx = state
        .current_goal()
        .expect("goal remains")
        .local_ctx
        .clone();
    let alpha_fvar = original_ctx[0].fvar;
    let witness_fvar = original_ctx[1].fvar;
    nontriviality_of(&mut state, Expr::fvar(alpha_fvar))
        .expect("nontriviality should create a proof-carrying continuation");

    assert_eq!(state.goals().len(), 2);
    let lemma_goal = &state.goals()[0];
    let continuation_goal = &state.goals()[1];
    assert_eq!(lemma_goal.local_ctx.len(), 2);
    assert_eq!(continuation_goal.target, a_ty);
    assert_eq!(continuation_goal.local_ctx.len(), 3);
    assert_eq!(continuation_goal.local_ctx[2].name, "h_nontrivial");
    let introduced_fvar = continuation_goal.local_ctx[2].fvar;
    assert_meta_scope(&state, lemma_goal, &[alpha_fvar, witness_fvar]);
    assert_meta_scope(
        &state,
        continuation_goal,
        &[alpha_fvar, witness_fvar, introduced_fvar],
    );

    exact(&mut state, Expr::fvar(witness_fvar)).expect("existing instance proves the obligation");
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![]))
        .expect("close the continuation");

    assert!(state.is_complete());
    let proof = state
        .closed_proof()
        .expect("proof-carrying chain must yield a closed proof");
    TypeChecker::new(&env)
        .check_type(&proof, &original_target)
        .expect("kernel must accept the nontriviality proof chain");
}

#[test]
fn lift_unsupported_fails_closed_without_mutating_state() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let original_target = Expr::arrow(a_ty.clone(), a_ty);
    let mut state = ProofState::new(env, original_target);
    intro(&mut state, "x").expect("introduce x");

    let goal_before = state.current_goal().expect("goal remains").clone();
    let next_fvar_before = state.next_fvar;
    let meta_count_before = state.metas().iter().count();
    let root_assignment_before = state.metas().get_assignment(state.root_meta_id).cloned();

    let err = lift_with_config(
        &mut state,
        "x",
        None,
        LiftConfig::new().with_name("x_lifted").with_proof("hx"),
    )
    .expect_err("unsupported lift must fail closed");
    match err {
        TacticError::InvalidTarget { tactic, detail } => {
            assert_eq!(tactic, "lift");
            assert!(detail.contains("proof-carrying"));
            assert!(detail.contains("unproved placeholder"));
        }
        other => panic!("unexpected lift error: {other:?}"),
    }

    let goal_after = state.current_goal().expect("goal must be preserved");
    assert_eq!(goal_after.meta_id, goal_before.meta_id);
    assert_eq!(goal_after.target, goal_before.target);
    assert_eq!(goal_after.local_ctx.len(), goal_before.local_ctx.len());
    for (after, before) in goal_after.local_ctx.iter().zip(&goal_before.local_ctx) {
        assert_eq!(after.fvar, before.fvar);
        assert_eq!(after.name, before.name);
        assert_eq!(after.ty, before.ty);
        assert_eq!(after.value, before.value);
    }
    assert_eq!(state.next_fvar, next_fvar_before);
    assert_eq!(state.metas().iter().count(), meta_count_before);
    assert_eq!(
        state.metas().get_assignment(state.root_meta_id),
        root_assignment_before.as_ref()
    );
}
