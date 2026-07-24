// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[serial]
fn test_aesop_no_sorry_on_assumption() {
    // Goal: P with hp : P in context — must be solved without sorry
    reset_all_counters();
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p,
            value: None,
        }],
    );

    let before = sorry_count();
    let ax = axiom_snapshot();
    aesop(&mut state).expect("aesop should prove P from hp : P");
    let after = sorry_count();

    assert_eq!(
        before,
        after,
        "SORRY LEAK: aesop used {} sorry (expected 0)",
        after - before
    );
    assert_no_trusted_axiom_usage("aesop", "P from assumption", ax);
}

#[test]
#[serial]
fn test_aesop_no_sorry_on_intro_assumption() {
    // Goal: P → P — must be solved with intro + assumption, no sorry
    reset_all_counters();
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal = Expr::arrow(p.clone(), p);

    let mut state = ProofState::new(env, goal);

    let before = sorry_count();
    let ax = axiom_snapshot();
    aesop(&mut state).expect("aesop should prove P → P");
    let after = sorry_count();

    assert_eq!(
        before,
        after,
        "SORRY LEAK: aesop used {} sorry (expected 0)",
        after - before
    );
    assert_no_trusted_axiom_usage("aesop", "P -> P", ax);
}

#[test]
#[serial]
fn test_aesop_no_sorry_on_and_intro() {
    // Goal: P ∧ Q with hp : P, hq : Q in context
    reset_all_counters();
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let and = Expr::const_(Name::from_string("And"), vec![]);
    let goal = Expr::app(Expr::app(and, p.clone()), q.clone());

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hp".to_string(),
                ty: p,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hq".to_string(),
                ty: q,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    let ax = axiom_snapshot();
    aesop(&mut state).expect("aesop should prove P ∧ Q from hp, hq");
    let after = sorry_count();

    assert_eq!(
        before,
        after,
        "SORRY LEAK: aesop used {} sorry (expected 0)",
        after - before
    );
    assert_no_trusted_axiom_usage("aesop", "P /\\ Q from assumptions", ax);
}
