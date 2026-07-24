// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `and_neg` Tseitin coverage.

use super::support::{mk_binary_and_terms, mk_env_with_classical, mk_eq_int};
use super::{attempt_reconstruction, Expr, LocalContext, Name, Proof, TypeChecker};

fn expected_and_neg_type() -> Expr {
    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let and_pq = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("And"), vec![]),
            p_prop.clone(),
        ),
        q_prop.clone(),
    );
    let not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_prop);
    let not_q = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), q_prop);
    let inner = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_q),
        and_pq,
    );
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_p),
        inner,
    )
}

/// AndNeg basic reconstruction: step succeeds, stats correct, 0 trust sub-terms.
///
/// `and_neg` clause: `{not p, not q, And p q}`.
///
/// Part of #302.
#[test]
fn test_and_neg_binary_step_reconstructs() {
    let (mut terms, map, ay_p, ay_q, ay_and_pq, _ay_not_and_pq) = mk_binary_and_terms();

    let ay_not_p = terms.mk_not_raw(ay_p);
    let ay_not_q = terms.mk_not_raw(ay_q);

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndNeg,
        vec![ay_not_p, ay_not_q, ay_and_pq],
        vec![],
        vec![ay_and_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert_eq!(result.stats.rule_attempts.get("and_neg"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("and_neg"), Some(&1));
    assert!(
        result.proof_term.is_some(),
        "and_neg should produce a proof term"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "and_neg proof should have no trust sub-terms"
    );
}

/// AndNeg proof term type-checks through the kernel.
///
/// `and_neg` clause: `{not p, not q, And p q}`.
///
/// Part of #302.
#[test]
fn test_and_neg_binary_type_checks() {
    let env = mk_env_with_classical();
    let (mut terms, map, ay_p, ay_q, ay_and_pq, _ay_not_and_pq) = mk_binary_and_terms();

    let ay_not_p = terms.mk_not_raw(ay_p);
    let ay_not_q = terms.mk_not_raw(ay_q);

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndNeg,
        vec![ay_not_p, ay_not_q, ay_and_pq],
        vec![],
        vec![ay_and_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("and_neg should produce a proof term");

    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("and_neg proof term should type-check");

    let expected = expected_and_neg_type();

    assert!(
        tc.is_def_eq(&ty, &expected),
        "and_neg proof type should be def-eq to Or (Not p) (Or (Not q) (And p q))"
    );
}
