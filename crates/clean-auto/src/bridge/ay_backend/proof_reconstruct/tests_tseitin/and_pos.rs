// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `and_pos` Tseitin coverage.

use super::support::{mk_binary_and_terms, mk_env_with_classical, mk_eq_int};
use super::{attempt_reconstruction, Expr, LocalContext, Name, Proof, TypeChecker};

/// AndPos(0) basic reconstruction: step succeeds, stats correct, 0 trust sub-terms.
///
/// `and_pos(0)` clause: `{not (And p q), p}`.
///
/// Part of #302.
#[test]
fn test_and_pos_binary_step_reconstructs() {
    let (terms, map, ay_p, _ay_q, ay_and_pq, ay_not_and_pq) = mk_binary_and_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndPos(0),
        vec![ay_not_and_pq, ay_p],
        vec![],
        vec![ay_and_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert_eq!(result.stats.rule_attempts.get("and_pos"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("and_pos"), Some(&1));
    assert!(
        result.proof_term.is_some(),
        "and_pos should produce a proof term"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "and_pos proof should have no trust sub-terms"
    );
}

/// AndPos(0) proof term type-checks through the kernel.
///
/// `and_pos(0)` clause: `{not (And p q), p}`.
///
/// Part of #302.
#[test]
fn test_and_pos_binary_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, ay_p, _ay_q, ay_and_pq, ay_not_and_pq) = mk_binary_and_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndPos(0),
        vec![ay_not_and_pq, ay_p],
        vec![],
        vec![ay_and_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("and_pos should produce a proof term");

    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("AndPos(0) proof term should type-check");

    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let and_pq = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("And"), vec![]),
            p_prop.clone(),
        ),
        q_prop,
    );
    let not_and_pq = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), and_pq);
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_and_pq),
        p_prop,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "and_pos(0) proof type should be def-eq to Or (Not (And p q)) p"
    );
}

/// AndPos(1) extracts the second conjunct: type-checks through the kernel.
///
/// `and_pos(1)` clause: `{not (And p q), q}`.
///
/// Part of #302.
#[test]
fn test_and_pos_second_conjunct_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, _ay_p, ay_q, ay_and_pq, ay_not_and_pq) = mk_binary_and_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndPos(1),
        vec![ay_not_and_pq, ay_q],
        vec![],
        vec![ay_and_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("and_pos(1) should produce a proof term");

    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("AndPos(1) proof term should type-check");

    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let and_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_prop),
        q_prop.clone(),
    );
    let not_and_pq = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), and_pq);
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_and_pq),
        q_prop,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "and_pos(1) proof type should be def-eq to Or (Not (And p q)) q"
    );
}
