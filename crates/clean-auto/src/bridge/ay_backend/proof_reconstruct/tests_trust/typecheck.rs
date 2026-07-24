// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_trust_proof_term_type_checks_in_kernel() {
    use clean_kernel::{Declaration, Environment, LocalContext, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    for name in ["TestP", "TestQ"] {
        let add_result = env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        });
        assert!(add_result.is_ok(), "add {name}: {:?}", add_result.err());
    }

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let prop_q = Expr::const_(Name::from_string("TestQ"), vec![]);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_var("q", prop_q.clone(), Expr::prop());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p, q], vec![], vec![]);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .expect("Trust should produce a proof term");

    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let inferred_type = tc
        .infer_type(&proof_term)
        .expect("Trust proof term should type-check");
    let expected_type = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), prop_p),
        prop_q,
    );

    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "Trust proof type should be def-eq to (Or TestP TestQ), got {inferred_type:?}"
    );
}

#[test]
fn test_trust_single_literal_type_checks_in_kernel() {
    use clean_kernel::{Declaration, Environment, LocalContext, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TestP"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add TestP");

    let (terms, map, proof, negated_goal) = mk_trust_single_literal();
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .expect("Trust single-literal should produce a proof term");

    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let inferred_type = tc
        .infer_type(&proof_term)
        .expect("Single-literal trust proof term should type-check");

    let expected_type = Expr::const_(Name::from_string("TestP"), vec![]);
    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "Trust proof type should be def-eq to TestP, got {inferred_type:?}"
    );
}

#[test]
fn test_trust_empty_clause_type_checks_in_kernel() {
    use clean_kernel::{Environment, LocalContext, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let terms = TermStore::new();
    let map = VariableMapping::new();

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .expect("Trust empty clause should produce a proof term");

    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let inferred_type = tc
        .infer_type(&proof_term)
        .expect("Empty-clause trust proof term should type-check");

    let expected_type = Expr::const_(Name::from_string("False"), vec![]);
    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "Trust proof type should be def-eq to False, got {inferred_type:?}"
    );
}

#[test]
fn test_trust_plus_resolution_composed_proof_type_checks_in_kernel() {
    let env = mk_env_with_test_prop();
    let (mut terms, map, prop_p, h_p_id, p) = mk_p_hypothesis();
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h_assume = proof.add_assume(p, None);
    let h_trust = proof.add_rule_step(AletheRule::Trust, vec![not_p], vec![], vec![]);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![h_assume, h_trust],
        vec![],
    );

    let negated_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(result.stats.reconstructed_steps, 3);
    assert!(result.derives_empty_clause);
    assert_eq!(result.trust_subterm_count, 1);

    let proof_term = result
        .proof_term
        .clone()
        .expect("Trust + Resolution should produce proof");
    assert_composed_proof_type_checks_to_false(
        &env,
        &result,
        proof_term,
        &prop_p,
        &negated_goal,
        h_p_id,
        "Trust + Resolution composed proof",
    );
}
