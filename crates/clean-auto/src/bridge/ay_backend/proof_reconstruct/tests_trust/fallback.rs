// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bridge::ay_backend::proof_reconstruct::ReconstructionResult;

#[test]
fn test_failed_step_trust_subterm_prevents_cascade() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let h_p_id = FVarId::new(10);

    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p.clone());

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h_hole = proof.add_rule_step(AletheRule::Hole, vec![not_p], vec![], vec![]);
    let h_assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![h_hole, h_assume],
        vec![],
    );

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_fallback_steps, 1);
    assert_eq!(result.stats.local_gap_steps, 1);
    assert_eq!(
        result.stats.trust_subterm_steps, 1,
        "Hole should synthesize exactly one trust sub-term, got {}",
        result.stats.trust_subterm_steps,
    );
    assert!(result.derives_empty_clause);
    assert!(result.proof_term.is_some());
    assert_eq!(result.trust_subterm_count, 1);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap)
    );
    let proof_term = result
        .proof_term
        .expect("proof term should be present after cascade prevention");
    assert_eq!(count_trusted_ay_in_expr(&proof_term), 1);
}

#[test]
fn test_cascade_prevention_composed_proof_type_checks_in_kernel() {
    let env = mk_env_with_test_prop();
    let (mut terms, map, prop_p, h_p_id, p) = mk_p_hypothesis();
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h_hole = proof.add_rule_step(AletheRule::Hole, vec![not_p], vec![], vec![]);
    let h_assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![h_hole, h_assume],
        vec![],
    );

    let negated_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_fallback_steps, 1);
    assert!(result.derives_empty_clause);

    let proof_term = result
        .proof_term
        .clone()
        .expect("cascade prevention should produce proof");
    assert_composed_proof_type_checks_to_false(
        &env,
        &result,
        proof_term,
        &prop_p,
        &negated_goal,
        h_p_id,
        "cascade-prevention composed proof",
    );
}

#[test]
fn test_unreachable_failed_step_is_pruned_from_fallback_stats() {
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
    let _h_hole_q = proof.add_rule_step(AletheRule::Hole, vec![q], vec![], vec![]);
    let h_hole_np = proof.add_rule_step(AletheRule::Hole, vec![not_p], vec![], vec![]);
    let h_assume = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![h_hole_np, h_assume],
        vec![],
    );

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.trust_fallback_steps, 1);
    assert_eq!(result.stats.local_gap_steps, 1);
    assert_eq!(
        result.stats.trust_subterm_steps, 1,
        "only the reachable Hole step should synthesize a trust sub-term, got {}",
        result.stats.trust_subterm_steps,
    );
    assert!(result.proof_term.is_some());
    assert!(result.derives_empty_clause);
    assert_eq!(result.trust_subterm_count, 1);
    assert_eq!(
        result.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap)
    );
    let proof_term = result
        .proof_term
        .expect("proof term should be present after dual cascade prevention");
    assert_eq!(count_trusted_ay_in_expr(&proof_term), 1);
}

/// When `build_trusted_ay_subterm_for_clause` fails because the clause contains
/// a ay term not present in the var_map, `synthesize_trust_subterm_for_step`
/// returns `None`. This test keeps the proof rootless so all steps are still
/// visited after reachable-root pruning: the unmapped Hole hits the
/// `inspect_err(...).ok()` path, the mapped Hole still produces a trust
/// sub-term, and a downstream Or step can reuse only the mapped premise.
///
/// Part of #2741: this exercises the logged `inspect_err(...).ok()` path in
/// `trust.rs` where trust-subterm synthesis fails for an unmapped clause.
fn run_untranslatable_clause_fallback_case() -> ReconstructionResult {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let p = terms.mk_var("p", Sort::Bool);
    // Create ay var `unmapped` that is NOT registered in the var_map.
    let unmapped = terms.mk_var("unmapped", Sort::Bool);

    map.register_var("p", prop_p.clone(), Expr::prop());

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    // Hole step with unmapped clause literal — translate_clause_props will fail.
    let _h_hole = proof.add_rule_step(AletheRule::Hole, vec![unmapped], vec![], vec![]);
    // Hole step with mapped literal — translate_clause_props succeeds.
    let h_hole_np = proof.add_rule_step(AletheRule::Hole, vec![not_p], vec![], vec![]);
    proof.add_rule_step(AletheRule::Or, vec![not_p], vec![h_hole_np], vec![]);

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    attempt_reconstruction(&proof, &terms, &map, &negated_goal)
}

#[test]
fn test_untranslatable_clause_fallback_without_subterm() {
    let result = run_untranslatable_clause_fallback_case();
    // Both Hole steps fail reconstruction → both counted as trust_fallback.
    assert_eq!(
        result.stats.trust_fallback_steps, 2,
        "both Hole steps should be counted as trust fallback"
    );
    assert_eq!(result.stats.local_gap_steps, 2);
    // Only the mapped Hole step (¬p) produces a trust subterm.
    // The unmapped Hole step fails silently — this is the diagnostic gap.
    assert_eq!(
        result.stats.trust_subterm_steps, 1,
        "only the translatable Hole step should produce a trust subterm; \
         the untranslatable step drops the proof term after logging the \
         synthesis error"
    );
    // The downstream Or step still succeeds because it only references
    // the mapped Hole step, not the unmapped one.
    assert!(
        result.proof_term.is_some(),
        "downstream resolution using the mapped step should succeed"
    );
    assert!(
        !result.derives_empty_clause,
        "the rootless fallback probe should stay on the non-contradiction path"
    );
    // The trust_subterm_count reflects only the successfully synthesized
    // subterms, not the total fallback count.
    assert_eq!(
        result.trust_subterm_count, 1,
        "trust_subterm_count should match trust_subterm_steps"
    );
    let proof_term = result
        .proof_term
        .expect("downstream Or step should reuse the mapped trust sub-term");
    assert_eq!(count_trusted_ay_in_expr(&proof_term), 1);
}
