// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for enhanced contradiction, exfalso, and absurd tactics.
//!
//! Tests patterns added beyond the base connective.rs implementation:
//! - `h : True = False` / `h : False = True`
//! - Constructor discrimination within contradiction search
//! - `eval_absurd` proof composition
//! - `classify_constructor_equality` helper

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level};

use super::combinators::TacticCtx;
use super::contradiction::{eval_absurd, eval_contradiction, eval_exfalso};
use super::core::{LocalDecl, ProofState, TacticError};
use super::injection::classify_constructor_equality;

/// Environment with True, False, Eq, absurd, and propositions P, Q.
fn setup_env_contradiction() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_eq().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    env
}

/// Environment with Nat inductive for constructor discrimination tests.
fn setup_env_nat_eq() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: prop,
    })
    .unwrap();

    env
}

// =========================================================================
// eval_contradiction: Pattern 1 — h : False
// =========================================================================

#[test]
fn test_eval_contradiction_false_hyp() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: false_type,
            value: None,
        }],
    );

    let mut ctx = TacticCtx::new(&mut state);
    eval_contradiction(&mut ctx).expect("contradiction with h : False should succeed");
    assert!(state.is_complete(), "goal should be closed");
}

// =========================================================================
// eval_contradiction: Pattern 4 — h1 : P, h2 : ¬P
// =========================================================================

#[test]
fn test_eval_contradiction_p_and_not_p() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let not_p = Expr::pi(BinderInfo::Default, p_type.clone(), false_type);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: p_type,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: not_p,
                value: None,
            },
        ],
    );

    let mut ctx = TacticCtx::new(&mut state);
    eval_contradiction(&mut ctx).expect("contradiction with P and ¬P should succeed");
    assert!(state.is_complete(), "goal should be closed");
}

// =========================================================================
// eval_contradiction: no contradiction found
// =========================================================================

#[test]
fn test_eval_contradiction_no_match() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: p_type,
            value: None,
        }],
    );

    let mut ctx = TacticCtx::new(&mut state);
    let err = eval_contradiction(&mut ctx).unwrap_err();
    assert!(
        matches!(err, TacticError::NoProgress { .. }),
        "should report no progress, got: {err:?}"
    );
}

// =========================================================================
// eval_contradiction: no goals
// =========================================================================

#[test]
fn test_eval_contradiction_no_goals() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let mut ctx = TacticCtx::new(&mut state);
    let err = eval_contradiction(&mut ctx).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "should report no goals, got: {err:?}"
    );
}

// =========================================================================
// eval_exfalso
// =========================================================================

#[test]
fn test_eval_exfalso_changes_goal() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    let mut ctx = TacticCtx::new(&mut state);
    eval_exfalso(&mut ctx).expect("exfalso should succeed");

    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    assert_eq!(state.goals().len(), 1);
    assert_eq!(state.goals()[0].target, false_type, "goal should be False");
}

// =========================================================================
// eval_absurd
// =========================================================================

#[test]
fn test_eval_absurd_closes_goal() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let not_p = Expr::pi(BinderInfo::Default, p_type.clone(), false_type);

    // Add proof witnesses to the environment
    let mut env_with_witnesses = env;
    env_with_witnesses
        .add_decl(Declaration::Axiom {
            name: Name::from_string("hp"),
            level_params: vec![],
            type_: p_type,
        })
        .unwrap();
    env_with_witnesses
        .add_decl(Declaration::Axiom {
            name: Name::from_string("hnp"),
            level_params: vec![],
            type_: not_p,
        })
        .unwrap();

    let mut state = ProofState::new(env_with_witnesses, target);

    let proof = Expr::const_(Name::from_string("hp"), vec![]);
    let neg_proof = Expr::const_(Name::from_string("hnp"), vec![]);

    eval_absurd(&mut state, proof, neg_proof).expect("absurd should close the goal");
    assert!(state.is_complete(), "goal should be closed after absurd");
}

#[test]
fn test_eval_absurd_type_mismatch() {
    let env = setup_env_contradiction();
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let q_type = Expr::const_(Name::from_string("Q"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    // neg_proof has type Q → False, but proof has type P
    let not_q = Expr::pi(BinderInfo::Default, q_type, false_type);

    let mut env_with = env;
    env_with
        .add_decl(Declaration::Axiom {
            name: Name::from_string("hp"),
            level_params: vec![],
            type_: p_type,
        })
        .unwrap();
    env_with
        .add_decl(Declaration::Axiom {
            name: Name::from_string("hnq"),
            level_params: vec![],
            type_: not_q,
        })
        .unwrap();

    let mut state = ProofState::new(env_with, target);

    let proof = Expr::const_(Name::from_string("hp"), vec![]);
    let neg_proof = Expr::const_(Name::from_string("hnq"), vec![]);

    let err = eval_absurd(&mut state, proof, neg_proof).unwrap_err();
    assert!(
        matches!(err, TacticError::TypeMismatch { .. }),
        "absurd with mismatched types should fail, got: {err:?}"
    );
}

// =========================================================================
// classify_constructor_equality
// =========================================================================

#[test]
fn test_classify_same_constructor() {
    let env = setup_env_nat_eq();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // Nat.succ needs an argument: use axiom constants a, b : Nat
    let mut env_with = env;
    for name in ["a", "b"] {
        env_with
            .add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: nat.clone(),
            })
            .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let succ_a = Expr::app(succ.clone(), a);
    let succ_b = Expr::app(succ, b);

    // Build @Eq.{1} Nat (Nat.succ a) (Nat.succ b) — same constructor
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            succ_a,
        ),
        succ_b,
    );

    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let state = ProofState::new(env_with.clone(), target.clone());
    let goal = state.current_goal().unwrap();

    // Sanity: verify constructors are registered
    assert!(
        env_with
            .get_constructor(&Name::from_string("Nat.succ"))
            .is_some(),
        "Nat.succ should be a registered constructor"
    );

    let result = classify_constructor_equality(&state, goal, &eq_ty);
    assert!(
        matches!(result, Some((true, ref name)) if name == "Nat.succ"),
        "should classify as same-constructor (injection), got: {result:?}"
    );
}

#[test]
fn test_classify_different_constructors() {
    let env = setup_env_nat_eq();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let mut env_with = env;
    env_with
        .add_decl(Declaration::Axiom {
            name: Name::from_string("n"),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let succ_n = Expr::app(succ, n);

    // Build @Eq.{1} Nat Nat.zero (Nat.succ n) — different constructors
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        succ_n,
    );

    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let state = ProofState::new(env_with.clone(), target);
    let goal = state.current_goal().unwrap();

    // Sanity: verify constructors are registered
    assert!(
        env_with
            .get_constructor(&Name::from_string("Nat.zero"))
            .is_some(),
        "Nat.zero should be a registered constructor"
    );

    let result = classify_constructor_equality(&state, goal, &eq_ty);
    assert!(
        matches!(result, Some((false, ref name)) if name == "Nat.zero"),
        "should classify as different-constructors (discriminate), got: {result:?}"
    );
}

#[test]
fn test_classify_non_constructor_equality() {
    let env = setup_env_contradiction();
    let p_type = Expr::const_(Name::from_string("P"), vec![]);

    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap();

    // Not an equality at all
    let result = classify_constructor_equality(&state, goal, &p_type);
    assert!(
        result.is_none(),
        "non-equality should return None, got: {result:?}"
    );
}
