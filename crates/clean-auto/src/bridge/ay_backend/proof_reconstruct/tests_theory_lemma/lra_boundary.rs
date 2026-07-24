// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::boundary::assert_lra_boundary_description_starts_with;
use super::support::semantic::{
    mk_raw_le, register_int_const, register_int_var, register_real_var,
};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, ReconstructionError, Sort,
    TermStore, VariableMapping,
};

#[test]
fn test_theory_lemma_unsupported_arithmetic() {
    // LRA theory lemma should return UnsupportedStep (not panic)
    let mut terms = TermStore::new();
    let map = VariableMapping::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let lt_ab = terms.mk_app(
        ay_core::Symbol::Named("<".to_string()),
        vec![a, b],
        Sort::Bool,
    );

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas("LRA", vec![lt_ab], FarkasAnnotation::from_ints(&[1]));

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.trust_fallback_steps, 1,
        "LRA theory lemma should fall back to trust"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_disconnected_bounds_fail_semantic_validation() {
    // LRA Farkas: {¬(a ≤ b), ¬(c ≤ d)} with Farkas certificate [1, 1].
    // The active subset is semantically malformed because the variables do not
    // eliminate in the linear combination, so this should stop at the validator.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

// test_theory_lemma_lra_farkas_three_bounds_mixed_reconstructed moved to
// lra_chain.rs as test_theory_lemma_lra_farkas_three_bounds_mixed_chain_symbolic
// (#2903: valid symbolic chain, not a malformed certificate).

#[test]
fn test_theory_lemma_lra_farkas_zero_coefficient_ignores_symbolic_tail() {
    // Zero-coefficient symbolic literals must not block additive reconstruction.
    // Post-#2896 this is the remaining direct success-path boundary fixture:
    // active bounds ¬(3≤2), ¬(5≤4); trailing ¬(x≤y) has coefficient 0 and
    // should be ignored by the contradiction builder.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let le_5_4 = mk_raw_le(&mut terms, five, four);
    let le_xy = terms.mk_le(x, y);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);
    let not_le_xy = terms.mk_not(le_xy);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 0]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4, not_le_xy], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "zero-coefficient symbolic tail should reconstruct exactly one theory-lemma step: {:?}",
        result.stats.first_diagnostic
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 0,
        "zero-coefficient symbolic tail should stay off the trust boundary"
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 0,
        "zero-coefficient symbolic tail should not fall back to trust"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_concrete_single_bound_with_active_symbolic_tail_hits_semantic_boundary(
) {
    // Even with one concretely contradictory bound, an additional active
    // symbolic bound keeps the full active subset semantically invalid.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_5_3 = mk_raw_le(&mut terms, five, three);
    let le_xy = terms.mk_le(x, y);
    let not_le_5_3 = terms.mk_not(le_5_3);
    let not_le_xy = terms.mk_not(le_xy);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_3, not_le_xy], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_in_resolution_chain() {
    // LRA Farkas used as premise in resolution.
    // The theory lemma hits the LRA trust boundary, but trust sub-term
    // synthesis (#302 W4 2534) creates a trustedAy sub-term for step 0.
    // This allows the downstream resolution step to succeed (no cascade
    // failure), though the final proof carries trust debt.
    //
    // Step 0: TheoryLemma {¬(a ≤ b), ¬(c ≤ d)} (LRA Farkas) → trust boundary + trust sub-term
    // Step 1: Assume {a ≤ b} → reconstructed
    // Step 2: Resolution on steps 0,1 → reconstructed (via trust sub-term)
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let tl = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd], farkas);

    // Assume a ≤ b (as the bound itself, wrapped in Or)
    let le_ab_clause = terms.mk_or(vec![le_ab]);
    let h_assume = proof.add_assume(le_ab_clause, None);

    // Resolve: {¬(a ≤ b), ¬(c ≤ d)} + {a ≤ b} → {¬(c ≤ d)}
    // Pivot: ¬(a ≤ b) in tl, a ≤ b in h_assume
    proof.add_resolution(vec![not_le_cd], not_le_ab, tl, h_assume);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.total_steps, 3);
    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(result.stats.resolution_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 2,
        "Assume + Resolution should both reconstruct (Resolution uses trust sub-term from step 0), got reconstructed={} with error: {:?}",
        result.stats.reconstructed_steps, result.stats.error,
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "the theory-lemma premise should be counted as a trust boundary"
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 1,
        "only the theory lemma should fall back (resolution succeeds via trust sub-term)"
    );
    assert!(
        result.proof_term.is_some(),
        "resolution should produce a proof term (with trust debt from sub-term)"
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("expected first_diagnostic for failing theory lemma");
    assert_eq!(diagnostic.step_index, Some(0));
    assert!(
        matches!(&diagnostic.error, ReconstructionError::TrustBoundary { .. }),
        "first error should be the theory-lemma trust boundary, got {:?}",
        diagnostic.error
    );
}

#[test]
fn test_theory_lemma_lra_farkas_le_trans_chain() {
    // Same-sort chain topology alone is not enough: x and y remain unmatched
    // in the active linear combination, so this should fail semantic validation
    // before chain closeout is considered.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    // Bounds: x ≤ b and b ≤ y — these chain via shared term b
    let le_xb = terms.mk_le(x, b);
    let le_by = terms.mk_le(b, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_le_by = terms.mk_not(le_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_le_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_reverse_chain() {
    // Reverse chain topology still fails semantic validation when the active
    // subset leaves symbolic endpoints unmatched.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let le_by = terms.mk_le(b, y);
    let le_xb = terms.mk_le(x, b);
    let not_le_by = terms.mk_not(le_by);
    let not_le_xb = terms.mk_not(le_xb);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    // Note: order is reversed compared to the forward chain test
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_by, not_le_xb], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_certificate_length_mismatch() {
    // Farkas certificate length (1) != clause length (2) → should error
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    // Certificate has 1 coeff but clause has 2 literals
    let farkas = FarkasAnnotation::from_ints(&[1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    // Should fail reconstruction (certificate mismatch)
    assert_eq!(
        result.stats.reconstructed_steps, 0,
        "Certificate length mismatch should fail reconstruction"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_three_le_bounds_shuffled() {
    // The shuffled path is still semantically invalid because the active
    // combination leaves the end variables unmatched.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let le_bc = terms.mk_le(b, c);
    let le_cd = terms.mk_le(c, d);
    // Clause order: c≤d, a≤b, b≤c (shuffled)
    let not_le_cd = terms.mk_not(le_cd);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_bc = terms.mk_not(le_bc);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_cd, not_le_ab, not_le_bc], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_three_le_non_chaining_fail_semantic_validation() {
    // 3 Le bounds that do NOT form a chain: a ≤ b, c ≤ d, e ≤ f.
    // The active linear combination cannot eliminate any endpoints, so the
    // certificate is rejected at semantic validation.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);
    let e = register_int_var(&mut terms, &mut map, "fvar_5", 5);
    let f = register_int_var(&mut terms, &mut map, "fvar_6", 6);

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let le_ef = terms.mk_le(e, f);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);
    let not_le_ef = terms.mk_not(le_ef);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd, not_le_ef], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_real_sort_le_chain() {
    // The Real chain shape is still semantically invalid here because the
    // active linear combination leaves symbolic endpoints unmatched.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_real_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xb = terms.mk_le(x, b);
    let le_by = terms.mk_le(b, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_le_by = terms.mk_not(le_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_le_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_non_chaining_bounds_fail_semantic_validation() {
    // Two Le bounds that don't share an intermediate term.
    // Bounds: a ≤ b, c ≤ d (no shared term) with cert [1, 1].
    // The active subset is not a valid Farkas conflict because no variables
    // eliminate, so semantic validation must reject it.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_concrete_subset_additive_with_active_symbolic_hits_semantic_boundary(
) {
    // When 2+ concrete bounds form a contradictory additive sum but there is
    // also an active symbolic bound (coefficient > 0), the bridge validates
    // the full active subset first. The symbolic variables do not eliminate,
    // so this stops at semantic validation instead of taking the concrete
    // additive subset.
    //
    // Active bounds: ¬(3≤2), ¬(5≤4), ¬(x≤y) — all coefficient 1.
    // Concrete subset: {3≤2, 5≤4} would imply 8 ≤ 6, but the active symbolic
    // bound x≤y is still part of the certificate and invalidates the replay.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let le_5_4 = mk_raw_le(&mut terms, five, four);
    let le_xy = terms.mk_le(x, y);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);
    let not_le_xy = terms.mk_not(le_xy);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4, not_le_xy], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}
