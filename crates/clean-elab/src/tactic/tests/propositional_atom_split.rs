// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `tauto`'s bounded classical atom split (the `by_cases`
//! fallback reached only at a dead end) and its leaf enablers.
//!
//! Split from propositional.rs for file size; same harness and imports.
use super::*;

// =========================================================================
// tauto classical atom split tests (bounded by_cases fallback + leaf enablers)
// =========================================================================

/// Register `names` as opaque Prop atoms for classical-split tests.
fn add_prop_atoms(env: &mut Environment, names: &[&str]) {
    for name in names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
}

/// `head p q` for a binary propositional connective constant.
fn conn2(head: &str, p: &Expr, q: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(head), vec![]), p.clone()),
        q.clone(),
    )
}

/// App-form negation `Not p` (the spelling `¬p` elaborates to).
fn not_app(p: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone())
}

#[test]
fn test_tauto_atom_split_closes_iff_xor_canonical() {
    // The canonical classical class (xor_not_left core): from `h : P ↔ Q`
    // prove `(¬P ∧ ¬Q) ∨ (Q ∧ ¬¬P)`. Both Or injections and de Morgan
    // dead-end, so only the bounded classical atom split can close it.
    let mut env = setup_env_with_prop_ext();
    add_prop_atoms(&mut env, &["P", "Q"]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    let left = conn2("And", &not_app(&p), &not_app(&q));
    let right = conn2("And", &q, &not_app(&not_app(&p)));
    let target = conn2("Or", &left, &right);
    let goal_ty = Expr::pi(BinderInfo::Default, conn2("Iff", &p, &q), target);

    let mut state = ProofState::new(env, goal_ty);
    tauto(&mut state).expect("tauto should close the Iff/Xor-form goal via the atom split");
    assert!(
        state.is_complete(),
        "all goals should be closed after the atom split"
    );
}

#[test]
fn test_tauto_false_goal_modus_ponens_chain_closes() {
    // (P → Q) → P → ¬Q → False. The False branch must reach hypothesis
    // application (isolated solve_by_elim) and the App-form `Not Q`
    // hypothesis must count as applicable.
    let mut env = setup_env_with_prop_ext();
    add_prop_atoms(&mut env, &["P", "Q"]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    let goal_ty = Expr::arrow(
        Expr::arrow(p.clone(), q.clone()),
        Expr::arrow(p.clone(), Expr::arrow(not_app(&q), false_ty)),
    );

    let mut state = ProofState::new(env, goal_ty);
    tauto(&mut state).expect("tauto should chain modus ponens into the False goal");
    assert!(
        state.is_complete(),
        "the contradiction chain should close every goal"
    );
}

#[test]
fn test_tauto_iff_hypothesis_destructs_to_mp() {
    // (P ↔ Q) → P → Q. Preprocess must destruct the Iff hypothesis so
    // solve_by_elim can chain through its mp side.
    let mut env = setup_env_with_prop_ext();
    add_prop_atoms(&mut env, &["P", "Q"]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    let goal_ty = Expr::arrow(conn2("Iff", &p, &q), Expr::arrow(p.clone(), q.clone()));

    let mut state = ProofState::new(env, goal_ty);
    tauto(&mut state).expect("tauto should destruct the Iff hypothesis and apply mp");
    assert!(state.is_complete(), "mp chaining should close every goal");
}

#[test]
fn test_tauto_iff_mp_chain_to_false_closes() {
    // (P ↔ Q) → P → ¬Q → False: the br2 contradiction leaf of the canonical
    // class — requires the Iff destruct AND the isolated False-branch
    // solve_by_elim together.
    let mut env = setup_env_with_prop_ext();
    add_prop_atoms(&mut env, &["P", "Q"]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    let goal_ty = Expr::arrow(
        conn2("Iff", &p, &q),
        Expr::arrow(p.clone(), Expr::arrow(not_app(&q), false_ty)),
    );

    let mut state = ProofState::new(env, goal_ty);
    tauto(&mut state).expect("tauto should refute P with the Iff mp side");
    assert!(
        state.is_complete(),
        "the Iff contradiction leaf should close every goal"
    );
}

#[test]
fn test_tauto_atom_split_non_tautology_fails_cleanly() {
    // P ∨ Q is not a tautology: atom splits fire, spend budget, and must
    // roll back — tauto reports NoProgress and the untouched goal survives.
    let mut env = setup_env_with_prop_ext();
    add_prop_atoms(&mut env, &["P", "Q"]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = conn2("Or", &p, &q);

    let mut state = ProofState::new(env, target.clone());
    let err = tauto(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoProgress { .. }),
        "expected NoProgress on a non-tautology, got: {err:?}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "the unproved goal must survive the split rollbacks"
    );
    let goal = state.current_goal().expect("goal should survive");
    assert_eq!(
        goal.target, target,
        "failed splits must restore the original target"
    );
}
