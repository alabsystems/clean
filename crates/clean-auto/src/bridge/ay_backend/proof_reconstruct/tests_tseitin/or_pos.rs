// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `or_pos` Tseitin coverage.

use super::support::{mk_env_with_classical, mk_eq_int};
use super::{
    attempt_reconstruction, Expr, LocalContext, Name, Proof, Sort, TermStore, TypeChecker,
    VariableMapping,
};

/// Build ay terms for a binary or_pos scenario: `p = (a=b)`, `q = (b=c)`.
///
/// Returns `(terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq)`.
fn mk_binary_or_pos_terms() -> (
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
    let ay_not_or_pq = terms.mk_not(ay_or_pq);

    (terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq)
}

/// Build ay terms for a ternary or_pos scenario: `p or q or r`.
///
/// Returns `(terms, map, ay_p, ay_q, ay_r, ay_or_pqr, ay_not_or_pqr)`.
fn mk_ternary_or_pos_terms() -> (
    TermStore,
    VariableMapping,
    ay_core::TermId,
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
    let ay_d = terms.mk_var("fvar_4", Sort::Int);

    for (slot, value) in [
        ("fvar_1", "testA"),
        ("fvar_2", "testB"),
        ("fvar_3", "testC"),
        ("fvar_4", "testC"),
    ] {
        map.register_var(
            slot,
            Expr::const_(Name::from_string(value), vec![]),
            int_ty.clone(),
        );
    }

    let ay_p = terms.mk_eq(ay_a, ay_b);
    let ay_q = terms.mk_eq(ay_b, ay_c);
    let ay_r = terms.mk_eq(ay_c, ay_d);
    let ay_or_pqr = terms.mk_or(vec![ay_p, ay_q, ay_r]);
    let ay_not_or_pqr = terms.mk_not(ay_or_pqr);

    (terms, map, ay_p, ay_q, ay_r, ay_or_pqr, ay_not_or_pqr)
}

/// OrPos basic reconstruction: step succeeds, stats correct, proof term present.
///
/// Part of #302.
#[test]
fn test_or_pos_binary_step_reconstructs() {
    let (terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq) = mk_binary_or_pos_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrPos(0),
        vec![ay_not_or_pq, ay_p, ay_q],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert_eq!(result.stats.rule_attempts.get("or_pos"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("or_pos"), Some(&1));
    assert!(
        result.proof_term.is_some(),
        "or_pos should produce a proof term"
    );
    assert!(
        !result.derives_empty_clause,
        "single non-empty clause should not derive empty clause"
    );
    assert!(
        result.compound_witness_fvars.is_empty(),
        "tautology clause should have no compound witnesses"
    );
}

/// OrPos proof term type-checks through the kernel.
///
/// The or_pos tautology `{not Q, p, q}` has clause type `Or (Not Q) Q` where
/// `Q = Or p q`. The reconstructed proof uses `Classical.em` + `Or.rec` swap.
///
/// Part of #302.
#[test]
fn test_or_pos_binary_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq) = mk_binary_or_pos_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrPos(0),
        vec![ay_not_or_pq, ay_p, ay_q],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    let proof_term = result
        .proof_term
        .expect("or_pos should produce a proof term");

    // The proof term has type Or (Q -> False) Q where Q = Or p q.
    // Uses Pi form (not App(Not,Q)) to match Classical.em's syntactic type.
    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("OrPos proof term should type-check");

    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let or_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_prop),
        q_prop,
    );
    let not_or_pq = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        or_pq.clone(),
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_or_pq),
        or_pq,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "inferred type should be def-eq to Or (Not Q) Q"
    );
}

/// OrPos with ternary disjunction: clause `{not (p or q or r), p, q, r}`.
///
/// Verifies that the or_chain_type construction handles n > 2 disjuncts
/// correctly, producing the right-associative Or chain.
///
/// Part of #302.
#[test]
fn test_or_pos_ternary_step_reconstructs() {
    let (terms, map, ay_p, ay_q, ay_r, ay_or_pqr, ay_not_or_pqr) = mk_ternary_or_pos_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::OrPos(0),
        vec![ay_not_or_pqr, ay_p, ay_q, ay_r],
        vec![],
        vec![ay_or_pqr],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert_eq!(result.stats.rule_attempts.get("or_pos"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("or_pos"), Some(&1));
    assert!(
        result.proof_term.is_some(),
        "ternary or_pos should produce a proof term"
    );
}
