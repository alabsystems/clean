// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `or_neg` Tseitin coverage.

use super::support::{mk_env_with_classical, mk_eq_int};
use super::{
    attempt_reconstruction, Expr, LocalContext, Name, Proof, Sort, TermStore, TypeChecker,
    VariableMapping,
};

/// Build ay terms for an or_neg scenario: `Q = p or q`, negate the first disjunct.
///
/// Returns `(terms, map, ay_p, ay_q, ay_or_pq, ay_not_p)`.
fn mk_binary_or_neg_terms() -> (
    TermStore,
    VariableMapping,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a = terms.mk_var("fvar_1", Sort::Int);
    let ay_b = terms.mk_var("fvar_2", Sort::Int);
    let ay_c = terms.mk_var("fvar_3", Sort::Int);

    map.register_var(
        "fvar_1",
        Expr::const_(Name::from_string("testA"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_2",
        Expr::const_(Name::from_string("testB"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_3",
        Expr::const_(Name::from_string("testC"), vec![]),
        int_ty,
    );

    let ay_p = terms.mk_eq(ay_a, ay_b);
    let ay_q = terms.mk_eq(ay_b, ay_c);
    let ay_or_pq = terms.mk_or(vec![ay_p, ay_q]);
    let ay_not_p = terms.mk_not(ay_p);

    (terms, map, ay_p, ay_q, ay_or_pq, ay_not_p)
}

/// Build ay terms for an or_neg scenario that negates the second disjunct.
///
/// Returns `(terms, map, ay_or_pq, ay_not_q)`.
fn mk_second_disjunct_or_neg_terms(
) -> (TermStore, VariableMapping, ay_core::TermId, ay_core::TermId) {
    let (mut terms, map, _ay_p, ay_q, ay_or_pq, _ay_not_p) = mk_binary_or_neg_terms();
    let ay_not_q = terms.mk_not(ay_q);
    (terms, map, ay_or_pq, ay_not_q)
}

fn expected_or_neg_type(negated_prop: Expr) -> Expr {
    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let or_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_prop),
        q_prop,
    );
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), or_pq),
        negated_prop,
    )
}

/// OrNeg basic reconstruction: step succeeds, stats correct, proof term present.
///
/// `or_neg` clause: `{Q, not p}` where `Q = p or q`.
///
/// Part of #302.
#[test]
fn test_or_neg_binary_step_reconstructs() {
    let (terms, map, _ay_p, _ay_q, ay_or_pq, ay_not_p) = mk_binary_or_neg_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrNeg,
        vec![ay_or_pq, ay_not_p],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert_eq!(result.stats.rule_attempts.get("or_neg"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("or_neg"), Some(&1));
    assert!(
        result.proof_term.is_some(),
        "or_neg should produce a proof term"
    );
    assert!(
        !result.derives_empty_clause,
        "single non-empty clause should not derive empty clause"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "or_neg proof should have no trust sub-terms"
    );
}

/// OrNeg proof term type-checks through the kernel.
///
/// `or_neg` clause: `{Q, not p}` where `Q = p or q`.
///
/// Part of #302.
#[test]
fn test_or_neg_binary_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, _ay_p, _ay_q, ay_or_pq, ay_not_p) = mk_binary_or_neg_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrNeg,
        vec![ay_or_pq, ay_not_p],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("or_neg should produce a proof term");

    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("or_neg proof term should type-check");

    let not_p = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        mk_eq_int("testA", "testB"),
    );
    let expected = expected_or_neg_type(not_p);

    assert!(
        tc.is_def_eq(&ty, &expected),
        "or_neg proof type should be def-eq to Or (p or q) (Not p)"
    );
}

/// OrNeg negating the second disjunct: `{Q, not q}` where `Q = p or q`.
///
/// Verifies that the position finding correctly handles the non-first disjunct.
///
/// Part of #302.
#[test]
fn test_or_neg_second_disjunct_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, ay_or_pq, ay_not_q) = mk_second_disjunct_or_neg_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrNeg,
        vec![ay_or_pq, ay_not_q],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("or_neg should produce a proof term");

    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("or_neg proof for second disjunct should type-check");

    let not_q = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        mk_eq_int("testB", "testC"),
    );
    let expected = expected_or_neg_type(not_q);

    assert!(
        tc.is_def_eq(&ty, &expected),
        "or_neg proof type should be def-eq to Or (p or q) (Not q)"
    );
}
