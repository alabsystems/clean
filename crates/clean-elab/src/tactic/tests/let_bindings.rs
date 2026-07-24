// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for ProofState let-binding context preservation.

use super::*;

fn setup_env_with_predicate_proof() -> Environment {
    let mut env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::arrow(a_ty.clone(), Expr::prop()),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pa"),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
    })
    .unwrap();

    env
}

#[test]
fn test_exact_respects_goal_local_let_binding_value() {
    let env = setup_env_with_predicate_proof();
    let x_fvar = FVarId::new(10);
    let target = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(x_fvar),
    );
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: x_fvar,
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: Some(Expr::const_(Name::from_string("a"), vec![])),
        }],
    );

    exact(&mut state, Expr::const_(Name::from_string("pa"), vec![]))
        .expect("exact should use goal-local let-binding values during type checking");
    assert!(state.is_complete());
}

#[test]
fn test_exact_respects_elab_local_let_binding_value() {
    let env = setup_env_with_predicate_proof();
    let x_fvar = FVarId::new(10);
    let target = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(x_fvar),
    );
    let mut state = ProofState::with_elab_context(
        env,
        target,
        vec![LocalDecl {
            fvar: x_fvar,
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: Some(Expr::const_(Name::from_string("a"), vec![])),
        }],
    );

    exact(&mut state, Expr::const_(Name::from_string("pa"), vec![]))
        .expect("exact should use elaborator-local let-binding values during type checking");
    assert!(state.is_complete());
}
