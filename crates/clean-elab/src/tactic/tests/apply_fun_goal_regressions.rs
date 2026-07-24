// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;

fn add_apply_fun_goal_supporting_decls(env: &mut Environment) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ProofBox"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::type_()),
        ),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("mkProofBox"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("ProofBox"), vec![]),
                        Expr::bvar(1),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();
}

fn mk_proof_box(alpha: Expr, value: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("mkProofBox"), vec![]), alpha),
        value,
    )
}

#[test]
fn test_apply_fun_goal_rejects_dependent_codomain() {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_goal_supporting_decls(&mut env);

    let proof_ty = make_eq_n(
        Expr::const_(Name::from_string("x"), vec![]),
        Expr::const_(Name::from_string("y"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h1"),
        level_params: vec![],
        type_: proof_ty.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h2"),
        level_params: vec![],
        type_: proof_ty.clone(),
    })
    .unwrap();

    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
                proof_ty.clone(),
            ),
            Expr::const_(Name::from_string("h1"), vec![]),
        ),
        Expr::const_(Name::from_string("h2"), vec![]),
    );
    let mut state = ProofState::new(env, target);
    let initial_meta_id = state.current_goal().unwrap().meta_id;
    let original_goal = state.current_goal().unwrap().clone();
    let func = Expr::lam(
        BinderInfo::Default,
        proof_ty.clone(),
        mk_proof_box(proof_ty, Expr::bvar(0)),
    );

    let result = apply_fun_goal(&mut state, func);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref detail)) if detail.contains("dependent functions")),
        "apply_fun_goal should reject dependent codomains instead of creating an ill-typed equality goal: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "rejecting the rewrite must not record trusted fallback usage"
    );
    assert!(
        !state.metas().is_assigned(initial_meta_id),
        "rejecting the rewrite must not close the original goal"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "rejecting the rewrite must not add subgoals"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        original_goal.target,
        "rejecting the rewrite must leave the original goal unchanged"
    );
}
