// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_trust_single_literal_produces_subterm() {
    let (terms, map, proof, negated_goal) = mk_trust_single_literal();
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(
        result.trust_subterm_count, 1,
        "trust_subterm_count should be 1"
    );
    assert_eq!(result.stats.alethe_trust_steps, 1);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep)
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 0,
        "trust_fallback_steps should be 0 (Trust is handled, not error)"
    );

    let proof_term = result
        .proof_term
        .expect("Trust step should produce a proof term");
    let app = match proof_term.kind() {
        ExprKind::App(f, arg) => Some((f, arg)),
        _ => None,
    };
    assert!(
        app.is_some(),
        "expected App(trustedAy, clause_type), got {proof_term:?}"
    );
    let (f, arg) = app.expect("invariant: asserted trustedAy application");

    let trusted_head = match f.kind() {
        ExprKind::Const(name, levels) => Some((name, levels)),
        _ => None,
    };
    assert!(
        trusted_head.is_some(),
        "expected trustedAy constant, got {f:?}"
    );
    let (name, levels) = trusted_head.expect("invariant: asserted trustedAy const");
    assert_eq!(name.to_string(), "trustedAy");
    assert_eq!(levels.len(), 1, "expected one universe level");
    assert_eq!(levels[0], Level::zero(), "expected Level 0 (Prop)");

    let clause_const = match arg.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    };
    assert!(
        clause_const.is_some(),
        "expected TestP constant argument, got {arg:?}"
    );
    let clause_const = clause_const.expect("invariant: asserted TestP const");
    assert_eq!(
        clause_const.to_string(),
        "TestP",
        "expected TestP as the clause type"
    );
}

#[test]
fn test_trust_empty_clause_produces_false_subterm() {
    let terms = TermStore::new();
    let map = VariableMapping::new();

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(result.trust_subterm_count, 1);
    assert!(result.derives_empty_clause);

    let proof_term = result.proof_term.expect("should produce a proof term");
    let app = match proof_term.kind() {
        ExprKind::App(f, arg) => Some((f, arg)),
        _ => None,
    };
    assert!(
        app.is_some(),
        "expected App(trustedAy, False), got {proof_term:?}"
    );
    let (f, arg) = app.expect("invariant: asserted trustedAy false application");

    let trusted_head = match f.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    };
    assert!(
        trusted_head.is_some(),
        "expected trustedAy constant, got {f:?}"
    );
    let trusted_head = trusted_head.expect("invariant: asserted trustedAy const");
    assert_eq!(trusted_head.to_string(), "trustedAy");

    let false_const = match arg.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    };
    assert!(
        false_const.is_some(),
        "expected False constant, got {arg:?}"
    );
    let false_const = false_const.expect("invariant: asserted False const");
    assert_eq!(
        false_const.to_string(),
        "False",
        "expected False as clause type"
    );
}

#[test]
fn test_trust_premise_enables_downstream_resolution() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let h_p_id = FVarId::new(10);

    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p.clone());

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

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.trust_subterm_steps, 1,
        "expected 1 trust subterm"
    );
    assert_eq!(result.stats.trust_fallback_steps, 0);
    assert_eq!(
        result.stats.reconstructed_steps, 3,
        "all 3 steps (Assume + Trust + ThResolution) should reconstruct"
    );
    assert!(result.derives_empty_clause);
    assert!(result.proof_term.is_some());
    assert_eq!(result.trust_subterm_count, 1);
}

#[test]
fn test_multiple_trust_steps_tracked() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let prop_q = Expr::const_(Name::from_string("TestQ"), vec![]);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    map.register_var("p", prop_p, Expr::prop());
    map.register_var("q", prop_q, Expr::prop());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], vec![], vec![]);
    proof.add_rule_step(AletheRule::Trust, vec![q], vec![], vec![]);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_subterm_steps, 2);
    assert_eq!(result.stats.alethe_trust_steps, 2);
    assert_eq!(result.trust_subterm_count, 2);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    assert_eq!(result.stats.reconstructed_steps, 2);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep)
    );
}

#[test]
fn test_trust_rule_stats_tracked() {
    let (terms, map, proof, negated_goal) = mk_trust_single_literal();
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.rule_attempts.get("trust"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("trust"), Some(&1));
}

#[test]
fn test_unreachable_trust_step_is_pruned_from_subterm_count() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let prop_q = Expr::const_(Name::from_string("TestQ"), vec![]);
    let h_p_id = FVarId::new(10);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_var("q", prop_q, Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p.clone());

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h_assume = proof.add_assume(p, None);
    let h_trust1 = proof.add_rule_step(AletheRule::Trust, vec![not_p], vec![], vec![]);
    let _h_trust2 = proof.add_rule_step(AletheRule::Trust, vec![q], vec![], vec![]);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![h_assume, h_trust1],
        vec![],
    );

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(
        result.trust_subterm_count, 1,
        "only the reachable trust step should contribute trust debt"
    );

    let proof_term = result
        .proof_term
        .expect("should produce a proof term with trust sub-terms");
    let actual_count = count_trusted_ay_in_expr(&proof_term);

    assert_eq!(
        actual_count, result.trust_subterm_count,
        "reconstruction stats should match the reachable trustedAy occurrences"
    );
    assert!(
        actual_count >= 1,
        "expected at least 1 trustedAy in the proof term (from Trust(¬p))"
    );
}

#[test]
fn test_trust_multi_literal_clause_or_chain() {
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

    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(result.trust_subterm_count, 1);

    let proof_term = result
        .proof_term
        .expect("Trust with multi-literal clause should produce a proof term");
    let app = match proof_term.kind() {
        ExprKind::App(f, clause_type) => Some((f, clause_type)),
        _ => None,
    };
    assert!(
        app.is_some(),
        "expected App(trustedAy, clause_type), got {proof_term:?}"
    );
    let (f, clause_type) = app.expect("invariant: asserted trustedAy clause app");

    let trusted_head = match f.kind() {
        ExprKind::Const(name, levels) => Some((name, levels)),
        _ => None,
    };
    assert!(
        trusted_head.is_some(),
        "expected trustedAy constant, got {f:?}"
    );
    let (name, levels) = trusted_head.expect("invariant: asserted trustedAy const");
    assert_eq!(name.to_string(), "trustedAy");
    assert_eq!(levels.len(), 1);
    assert_eq!(levels[0], Level::zero());

    let outer_or = match clause_type.kind() {
        ExprKind::App(or_inner, _q_arg) => Some(or_inner),
        _ => None,
    };
    assert!(
        outer_or.is_some(),
        "expected Or application for multi-literal clause, got {clause_type:?}"
    );
    let outer_or = outer_or.expect("invariant: asserted outer Or app");

    let inner_or = match outer_or.kind() {
        ExprKind::App(or_const, _p_arg) => Some(or_const),
        _ => None,
    };
    assert!(inner_or.is_some(), "expected App(Or, _), got {outer_or:?}");
    let inner_or = inner_or.expect("invariant: asserted inner Or app");

    let or_const = match inner_or.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    };
    assert!(or_const.is_some(), "expected Or constant, got {inner_or:?}");
    let or_const = or_const.expect("invariant: asserted Or const");
    assert_eq!(or_const.to_string(), "Or");
}

#[test]
fn test_unreachable_theory_trust_is_pruned_from_subterm_count() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TheoryTrustP"), vec![]);
    let prop_q = Expr::const_(Name::from_string("TheoryTrustQ"), vec![]);
    let h_p_id = FVarId::new(10);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_var("q", prop_q, Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p.clone());

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("trust", vec![q], TheoryLemmaKind::BvBitBlast);
    let trust_np = proof.add_theory_lemma_with_kind(
        "trust",
        vec![not_p],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let h_assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![trust_np, h_assume],
        vec![],
    );

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    assert_eq!(result.stats.trust_subterm_steps, 1);
    assert_eq!(result.trust_subterm_count, 1);
    assert_eq!(result.stats.theory_bv_bitblast_steps, 0);
    assert_eq!(result.stats.theory_array_axiom_steps, 1);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaArrayAxiom)
    );
    assert!(result.derives_empty_clause);
    let proof_term = result
        .proof_term
        .expect("reachable trust-only theory lemma should allow final resolution");
    assert_eq!(count_trusted_ay_in_expr(&proof_term), 1);
}
