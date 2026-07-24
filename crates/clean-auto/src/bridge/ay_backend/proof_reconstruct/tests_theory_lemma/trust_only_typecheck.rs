// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    attempt_reconstruction, Expr, FVarId, Name, Proof, Sort, TermStore, TheoryLemmaKind,
    VariableMapping,
};
use ay_core::AletheRule;

fn mk_kernel_env(prop_names: &[&str]) -> clean_kernel::Environment {
    use clean_kernel::{Declaration, Environment};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");
    for prop_name in prop_names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(prop_name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("add proposition axiom");
    }
    env
}

fn assert_closed_proof_type_checks_to_expected(
    env: &clean_kernel::Environment,
    proof_term: &Expr,
    expected_type: &Expr,
    msg: &str,
) {
    use clean_kernel::{LocalContext, TypeChecker};

    let tc = TypeChecker::with_context(env, LocalContext::new());
    let inferred_type = tc
        .infer_type(proof_term)
        .expect("proof term should type-check");
    assert!(
        tc.is_def_eq(&inferred_type, expected_type),
        "{msg}: expected {:?}, got {:?}",
        expected_type,
        inferred_type,
    );
}

fn assert_composed_proof_type_checks_to_false(
    env: &clean_kernel::Environment,
    mut proof_term: Expr,
    prop_p: &Expr,
    negated_goal: &Expr,
    h_p_id: FVarId,
    negated_goal_fvar: Option<FVarId>,
    msg: &str,
) {
    use clean_kernel::{BinderInfo, LocalContext, TypeChecker};

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("h_p"),
        prop_p.clone(),
        BinderInfo::Default,
    );
    if let Some(sentinel_id) = negated_goal_fvar {
        let normal_neg_id = FVarId::new(32);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            negated_goal.clone(),
            BinderInfo::Default,
        );
    }

    let tc = TypeChecker::with_context(env, ctx);
    let inferred_type = tc
        .infer_type(&proof_term)
        .expect("composed proof term should type-check");
    let expected_type = Expr::const_(Name::from_string("False"), vec![]);
    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "{msg}: expected False, got {:?}",
        inferred_type,
    );
}

#[test]
fn test_theory_lemma_bv_bitblast_trust_subterm_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("BvTrustP"), vec![]);
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("trust", vec![p], TheoryLemmaKind::BvBitBlast);

    let negated_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .expect("BvBitBlast theory lemma should produce a proof term");

    let env = mk_kernel_env(&["BvTrustP"]);
    assert_closed_proof_type_checks_to_expected(
        &env,
        &proof_term,
        &prop_p,
        "BvBitBlast trust-only theory lemma",
    );
}

#[test]
fn test_theory_lemma_bv_bitblast_composed_proof_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("BvTrustResolveP"), vec![]);
    let h_p = FVarId::new(41);

    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_hypothesis("p", h_p, Expr::fvar(h_p), prop_p.clone());

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("trust", vec![not_p], TheoryLemmaKind::BvBitBlast);
    let assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![lemma, assume],
        vec![],
    );

    let negated_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .clone()
        .expect("BvBitBlast trust lemma plus ThResolution should produce a proof");

    let env = mk_kernel_env(&["BvTrustResolveP"]);
    assert_composed_proof_type_checks_to_false(
        &env,
        proof_term,
        &prop_p,
        &negated_goal,
        h_p,
        result.negated_goal_fvar,
        "BvBitBlast trust-only theory lemma plus ThResolution",
    );
}

#[test]
fn test_theory_lemma_array_axiom_composed_proof_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("ArrayTrustP"), vec![]);
    let h_p = FVarId::new(31);

    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_hypothesis("p", h_p, Expr::fvar(h_p), prop_p.clone());

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind(
        "trust",
        vec![not_p],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![lemma, assume],
        vec![],
    );

    let negated_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .clone()
        .expect("ArrayAxiom trust lemma plus ThResolution should produce a proof");

    let env = mk_kernel_env(&["ArrayTrustP"]);
    assert_composed_proof_type_checks_to_false(
        &env,
        proof_term,
        &prop_p,
        &negated_goal,
        h_p,
        result.negated_goal_fvar,
        "ArrayAxiom trust-only theory lemma plus ThResolution",
    );
}

#[test]
fn test_theory_lemma_generic_empty_clause_type_checks_in_kernel() {
    let terms = TermStore::new();
    let map = VariableMapping::new();

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("trust", vec![], TheoryLemmaKind::Generic);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    let proof_term = result
        .proof_term
        .expect("Generic trust theory lemma should produce a proof term");

    let env = mk_kernel_env(&[]);
    let expected_type = Expr::const_(Name::from_string("False"), vec![]);
    assert_closed_proof_type_checks_to_expected(
        &env,
        &proof_term,
        &expected_type,
        "Generic trust-only theory lemma empty clause",
    );
}
