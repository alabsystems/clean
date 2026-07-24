// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::boundary::assert_lra_trust_boundary;
use super::support::semantic::{register_int_const, register_int_var};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, TheoryLemmaKind,
    VariableMapping,
};

#[test]
fn test_theory_lemma_lia_generic_two_bounds_chaining() {
    // LiaGeneric with 2 chaining Le bounds over Int: {¬(x ≤ y), ¬(y ≤ z)}
    // Farkas certificate [1, 1]. Structurally identical to LRA Farkas but the
    // symbolic open endpoints still require a trust-boundary refusal.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let y = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let z = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xy = terms.mk_le(x, y);
    let le_yz = terms.mk_le(y, z);
    let not_le_xy = terms.mk_not(le_xy);
    let not_le_yz = terms.mk_not(le_yz);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_xy, not_le_yz],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lia_generic_three_bounds_mixed() {
    // LiaGeneric with 3 mixed Le/Lt bounds: {¬(a ≤ b), ¬(b < c), ¬(c ≤ d)}
    // Farkas certificate [1, 1, 1]. Tests that LiaGeneric delegates to the
    // same concrete closing path as LRA.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_const(&mut terms, &mut map, "const5", 5);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_ab = terms.mk_le(a, b);
    let lt_bc = terms.mk_lt(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_lt_bc = terms.mk_not(lt_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_ab, not_lt_bc, not_le_cd],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "LiaGeneric concrete mixed chain should be reconstructed, error: {:?}",
        result.stats.error,
    );
    assert!(
        result.proof_term.is_some(),
        "LiaGeneric concrete mixed chain should produce a proof term"
    );
}

#[test]
fn test_theory_lemma_lia_generic_without_farkas_returns_error() {
    // LiaGeneric without Farkas certificate should return UnsupportedStep.
    // This tests the defensive None arm in the dispatch.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let y = register_int_var(&mut terms, &mut map, "fvar_2", 2);

    let le_xy = terms.mk_le(x, y);
    let not_le_xy = terms.mk_not(le_xy);

    let mut proof = Proof::new();
    // Use add_theory_lemma_with_kind (no Farkas) to simulate missing certificate
    proof.add_theory_lemma_with_kind("LIA", vec![not_le_xy], TheoryLemmaKind::LiaGeneric);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    // Without Farkas, reconstruction should fail instead of synthesizing an arithmetic boundary proof.
    assert_eq!(
        result.stats.reconstructed_steps, 0,
        "LiaGeneric without Farkas should not reconstruct"
    );
    assert!(
        result.stats.error.is_some(),
        "Should have an error for missing Farkas certificate"
    );
}

#[test]
fn test_theory_lemma_lia_generic_without_farkas_uses_implicit_unit_fallback() {
    // Omitted LiaGeneric annotations still mean "all unit coefficients".
    // The fallback should therefore reconstruct the same concrete contradiction
    // as the explicit [1, 1, 1] case above.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_const(&mut terms, &mut map, "const5", 5);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_ab = terms.mk_le(a, b);
    let lt_bc = terms.mk_lt(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_lt_bc = terms.mk_not(lt_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "LIA",
        vec![not_le_ab, not_lt_bc, not_le_cd],
        TheoryLemmaKind::LiaGeneric,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "LiaGeneric omitted-annotation fallback should reconstruct the concrete contradiction, error: {:?}",
        result.stats.error,
    );
    assert!(
        result.proof_term.is_some(),
        "LiaGeneric omitted-annotation fallback should still produce a proof term"
    );
}

#[test]
fn test_theory_lemma_lia_generic_without_farkas_rejects_consistent_chain() {
    // The omitted-annotation fallback must not invent a contradiction for a
    // consistent chain. It should stop at the arithmetic trust boundary and
    // return no proof term because every reconstruction step failed (#2986).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let y = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let z = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xy = terms.mk_le(x, y);
    let le_yz = terms.mk_le(y, z);
    let not_le_xy = terms.mk_not(le_xy);
    let not_le_yz = terms.mk_not(le_yz);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "LIA",
        vec![not_le_xy, not_le_yz],
        TheoryLemmaKind::LiaGeneric,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_trust_boundary(&result, 0);
}
