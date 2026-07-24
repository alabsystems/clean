// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for XOR Tseitin clausification rule handlers.
//!
//! Tests xor_pos1, xor_pos2, xor_neg1, xor_neg2 kernel proof reconstruction
//! with type-checking through the clean kernel.
//!
//! Part of #302.

use super::{attempt_reconstruction, expr_builders, VariableMapping};
use ay::Sort;
use ay_core::{AletheRule, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};

fn mk_env_with_classical_props() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");

    let prop = Expr::sort(Level::zero());
    for name in ["testP", "testQ"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

fn mk_bool_xor_terms() -> (
    TermStore,
    VariableMapping,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop = Expr::sort(Level::zero());
    let ay_p = terms.mk_var("fvar_p", Sort::Bool);
    let ay_q = terms.mk_var("fvar_q", Sort::Bool);

    map.register_var(
        "fvar_p",
        Expr::const_(Name::from_string("testP"), vec![]),
        prop.clone(),
    );
    map.register_var(
        "fvar_q",
        Expr::const_(Name::from_string("testQ"), vec![]),
        prop,
    );

    let ay_xor = terms.mk_xor(ay_p, ay_q);
    let ay_not_xor = terms.mk_not_raw(ay_xor);
    let ay_not_p = terms.mk_not_raw(ay_p);
    let ay_not_q = terms.mk_not_raw(ay_q);

    (
        terms, map, ay_p, ay_q, ay_xor, ay_not_xor, ay_not_p, ay_not_q,
    )
}

fn mk_xor_prop() -> Expr {
    let p = Expr::const_(Name::from_string("testP"), vec![]);
    let q = Expr::const_(Name::from_string("testQ"), vec![]);
    expr_builders::mk_xor(&p, &q)
}

#[test]
fn test_xor_pos1_type_checks() {
    let env = mk_env_with_classical_props();
    let (terms, map, ay_p, ay_q, _ay_xor, ay_not_xor, _ay_not_p, _ay_not_q) = mk_bool_xor_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::XorPos1,
        vec![ay_not_xor, ay_p, ay_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    assert!(
        result.proof_term.is_some(),
        "xor_pos1 should produce a proof term, error: {:?}",
        result.stats.error,
    );
    assert_eq!(result.trust_subterm_count, 0);

    let proof_term = result.proof_term.unwrap();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .expect("xor_pos1 proof term should type-check");

    let xor = mk_xor_prop();
    let p = Expr::const_(Name::from_string("testP"), vec![]);
    let q = Expr::const_(Name::from_string("testQ"), vec![]);
    let expected =
        expr_builders::mk_or(&expr_builders::mk_not(&xor), &expr_builders::mk_or(&p, &q));

    assert!(
        tc.is_def_eq(&ty, &expected),
        "xor_pos1 proof type should be def-eq to Or (Not (xor p q)) (Or p q)"
    );
}

#[test]
fn test_xor_pos2_type_checks() {
    let env = mk_env_with_classical_props();
    let (terms, map, _ay_p, _ay_q, _ay_xor, ay_not_xor, ay_not_p, ay_not_q) = mk_bool_xor_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::XorPos2,
        vec![ay_not_xor, ay_not_p, ay_not_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    assert!(
        result.proof_term.is_some(),
        "xor_pos2 should produce a proof term"
    );
    assert_eq!(result.trust_subterm_count, 0);

    let proof_term = result.proof_term.unwrap();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .expect("xor_pos2 proof term should type-check");

    let xor = mk_xor_prop();
    let p = Expr::const_(Name::from_string("testP"), vec![]);
    let q = Expr::const_(Name::from_string("testQ"), vec![]);
    let expected = expr_builders::mk_or(
        &expr_builders::mk_not(&xor),
        &expr_builders::mk_or(&expr_builders::mk_not(&p), &expr_builders::mk_not(&q)),
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "xor_pos2 proof type should be def-eq to Or (Not (xor p q)) (Or (Not p) (Not q))"
    );
}

#[test]
fn test_xor_neg1_type_checks() {
    let env = mk_env_with_classical_props();
    let (terms, map, ay_p, _ay_q, ay_xor, _ay_not_xor, _ay_not_p, ay_not_q) = mk_bool_xor_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::XorNeg1,
        vec![ay_xor, ay_p, ay_not_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    assert!(
        result.proof_term.is_some(),
        "xor_neg1 should produce a proof term"
    );
    assert_eq!(result.trust_subterm_count, 0);

    let proof_term = result.proof_term.unwrap();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .expect("xor_neg1 proof term should type-check");

    let xor = mk_xor_prop();
    let p = Expr::const_(Name::from_string("testP"), vec![]);
    let q = Expr::const_(Name::from_string("testQ"), vec![]);
    let expected =
        expr_builders::mk_or(&xor, &expr_builders::mk_or(&p, &expr_builders::mk_not(&q)));

    assert!(
        tc.is_def_eq(&ty, &expected),
        "xor_neg1 proof type should be def-eq to Or (xor p q) (Or p (Not q))"
    );
}

#[test]
fn test_xor_neg2_type_checks() {
    let env = mk_env_with_classical_props();
    let (terms, map, _ay_p, ay_q, ay_xor, _ay_not_xor, ay_not_p, _ay_not_q) = mk_bool_xor_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::XorNeg2,
        vec![ay_xor, ay_not_p, ay_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    assert!(
        result.proof_term.is_some(),
        "xor_neg2 should produce a proof term"
    );
    assert_eq!(result.trust_subterm_count, 0);

    let proof_term = result.proof_term.unwrap();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let ty = tc
        .infer_type(&proof_term)
        .expect("xor_neg2 proof term should type-check");

    let xor = mk_xor_prop();
    let p = Expr::const_(Name::from_string("testP"), vec![]);
    let q = Expr::const_(Name::from_string("testQ"), vec![]);
    let expected =
        expr_builders::mk_or(&xor, &expr_builders::mk_or(&expr_builders::mk_not(&p), &q));

    assert!(
        tc.is_def_eq(&ty, &expected),
        "xor_neg2 proof type should be def-eq to Or (xor p q) (Or (Not p) q)"
    );
}
