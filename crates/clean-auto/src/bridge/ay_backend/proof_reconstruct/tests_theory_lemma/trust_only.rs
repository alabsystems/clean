// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    attempt_reconstruction, Expr, ExprKind, FVarId, Name, Proof, Sort, TermStore, TheoryLemmaKind,
    VariableMapping,
};
use crate::bridge::ay_backend::proof_reconstruct::ReconstructionResult;
use crate::bridge::ay_backend::{ResidualTrustSource, ResidualTrustSummary};
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

fn assert_trusted_ay_application(expr: &Expr, expected_arg: &str) {
    assert!(
        matches!(expr.kind(), ExprKind::App(_, _)),
        "expected trustedAy application, got {expr:?}"
    );
    let ExprKind::App(f, arg) = expr.kind() else {
        return;
    };
    assert!(
        matches!(f.kind(), ExprKind::Const(name, _) if name.to_string() == "trustedAy"),
        "expected trustedAy constant head, got {f:?}"
    );
    assert!(
        matches!(arg.kind(), ExprKind::Const(name, _) if name.to_string() == expected_arg),
        "expected clause type {expected_arg}, got {arg:?}"
    );
}

fn assert_handled_trust_only_stats(
    result: &ReconstructionResult,
    reconstructed_steps: usize,
    trust_subterm_count: usize,
    expected_source: ResidualTrustSource,
) {
    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(result.stats.reconstructed_steps, reconstructed_steps);
    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    assert_eq!(result.trust_subterm_count, trust_subterm_count);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(expected_source)
    );
    assert!(
        matches!(
            expected_source,
            ResidualTrustSource::TheoryLemmaBvBitBlast
                | ResidualTrustSource::TheoryLemmaArrayAxiom
                | ResidualTrustSource::TheoryLemmaGeneric
        ),
        "expected a trust-only theory lemma source, got {expected_source:?}"
    );
    if expected_source == ResidualTrustSource::TheoryLemmaBvBitBlast {
        assert_eq!(result.stats.theory_bv_bitblast_steps, 1);
    } else if expected_source == ResidualTrustSource::TheoryLemmaArrayAxiom {
        assert_eq!(result.stats.theory_array_axiom_steps, 1);
    } else if expected_source == ResidualTrustSource::TheoryLemmaGeneric {
        assert_eq!(result.stats.theory_generic_steps, 1);
    }
    assert!(
        result.stats.first_error.is_none(),
        "handled trust-only theory lemmas should not record first_error: {:?}",
        result.stats.first_error
    );
}

#[test]
fn test_theory_lemma_bv_bitblast_produces_trust_subterm() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("BvTrustP"), vec![]);
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("trust", vec![p], TheoryLemmaKind::BvBitBlast);

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    assert_handled_trust_only_stats(&result, 1, 1, ResidualTrustSource::TheoryLemmaBvBitBlast);

    let proof_term = result
        .proof_term
        .expect("BvBitBlast theory lemma should produce a proof term");
    assert_trusted_ay_application(&proof_term, "BvTrustP");

    let env = mk_kernel_env(&["BvTrustP"]);
    assert_closed_proof_type_checks_to_expected(
        &env,
        &proof_term,
        &Expr::const_(Name::from_string("BvTrustP"), vec![]),
        "BvBitBlast trust-only theory lemma",
    );
}

#[test]
fn test_theory_lemma_array_axiom_premise_enables_th_resolution() {
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

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    assert_handled_trust_only_stats(&result, 3, 1, ResidualTrustSource::TheoryLemmaArrayAxiom);
    assert!(
        result.derives_empty_clause,
        "array-axiom trust lemma plus assume should derive the empty clause"
    );
    assert!(
        result.proof_term.is_some(),
        "downstream ThResolution should succeed with the trust-carrying premise"
    );

    let proof_term = result
        .proof_term
        .clone()
        .expect("ArrayAxiom trust lemma plus ThResolution should produce a proof");
    let env = mk_kernel_env(&["ArrayTrustP"]);
    assert_composed_proof_type_checks_to_false(
        &env,
        proof_term,
        &Expr::const_(Name::from_string("ArrayTrustP"), vec![]),
        &negated_goal,
        h_p,
        result.negated_goal_fvar,
        "ArrayAxiom trust-only theory lemma plus ThResolution",
    );
}

#[test]
fn test_theory_lemma_generic_empty_clause_produces_false_trust_subterm() {
    let terms = TermStore::new();
    let map = VariableMapping::new();

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("trust", vec![], TheoryLemmaKind::Generic);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);
    assert_handled_trust_only_stats(&result, 1, 1, ResidualTrustSource::TheoryLemmaGeneric);
    assert!(result.derives_empty_clause);

    let proof_term = result
        .proof_term
        .expect("Generic trust theory lemma should produce a proof term");
    assert_trusted_ay_application(&proof_term, "False");

    let env = mk_kernel_env(&[]);
    assert_closed_proof_type_checks_to_expected(
        &env,
        &proof_term,
        &Expr::const_(Name::from_string("False"), vec![]),
        "Generic trust-only theory lemma empty clause",
    );
}
