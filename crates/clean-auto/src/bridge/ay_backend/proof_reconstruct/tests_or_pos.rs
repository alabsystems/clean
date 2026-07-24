// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused tests for the `or_pos` clausification proof builder.
//!
//! `or_pos` is currently forward-looking for when ay emits clausification
//! proof steps, but the handler already exists in `generic_step.rs`. Keep the
//! clause shape and kernel type behavior pinned so future wiring does not
//! regress the proof term construction.

use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{AletheRule, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};

fn mk_env_with_classical() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA", "testB", "testC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

fn mk_eq_int(x: &str, y: &str) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), int_ty),
            Expr::const_(Name::from_string(x), vec![]),
        ),
        Expr::const_(Name::from_string(y), vec![]),
    )
}

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

#[test]
fn test_or_pos_binary_step_reconstructs() {
    let (terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq) = mk_binary_or_pos_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::OrPos(0),
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
        "single non-empty clause should not derive the empty clause"
    );
    assert!(
        result.compound_witness_fvars.is_empty(),
        "or_pos tautologies should stay closed"
    );
}

#[test]
fn test_or_pos_binary_type_checks() {
    let env = mk_env_with_classical();
    let (terms, map, ay_p, ay_q, ay_or_pq, ay_not_or_pq) = mk_binary_or_pos_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::OrPos(0),
        vec![ay_not_or_pq, ay_p, ay_q],
        vec![],
        vec![ay_or_pq],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    let proof_term = result
        .proof_term
        .expect("or_pos should reconstruct into a proof term");

    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .expect("or_pos proof term should type-check");

    let p_prop = mk_eq_int("testA", "testB");
    let q_prop = mk_eq_int("testB", "testC");
    let disj = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_prop),
        q_prop,
    );
    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            Expr::app(Expr::const_(Name::from_string("Not"), vec![]), disj.clone()),
        ),
        disj,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "or_pos proof type should be def-eq to Or (Not (p ∨ q)) (p ∨ q)"
    );
}

#[test]
fn test_or_pos_ternary_step_reconstructs() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a = terms.mk_var("fvar_1", Sort::Int);
    let ay_b = terms.mk_var("fvar_2", Sort::Int);
    let ay_c = terms.mk_var("fvar_3", Sort::Int);
    let ay_d = terms.mk_var("fvar_4", Sort::Int);

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
        int_ty.clone(),
    );
    map.register_var(
        "fvar_4",
        Expr::const_(Name::from_string("testA"), vec![]),
        int_ty,
    );

    let ay_p = terms.mk_eq(ay_a, ay_b);
    let ay_q = terms.mk_eq(ay_b, ay_c);
    let ay_r = terms.mk_eq(ay_c, ay_d);
    let ay_or_pqr = terms.mk_or(vec![ay_p, ay_q, ay_r]);
    let ay_not_or_pqr = terms.mk_not(ay_or_pqr);

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::OrPos(0),
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
    assert!(
        result.compound_witness_fvars.is_empty(),
        "ternary or_pos tautologies should stay closed"
    );
}
