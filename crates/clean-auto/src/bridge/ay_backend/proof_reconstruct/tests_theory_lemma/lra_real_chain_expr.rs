// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Real-sort Farkas chain closing with concrete endpoints.
//!
//! These exercise chain reconstruction where the chain endpoints are native ay
//! Rational constants (via `mk_real_int_const`) with a symbolic Real variable
//! in between. The chain builder extracts concrete values from ay constants
//! and closes the contradiction.
//!
//! Part of #302.

use super::support::semantic::{mk_real_int_const, register_real_var};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, VariableMapping,
};

#[test]
fn test_theory_lemma_lra_farkas_real_chain_concrete_expr_nonneg() {
    // Real-sort chain with concrete non-negative endpoints as native ay
    // Rational constants. The chain builder extracts concrete values directly
    // from ay ConstantView::Rational.
    //
    // Bounds: ¬(5 ≤ x), ¬(x ≤ 3) → chain: 5 ≤ x ≤ 3 → 5 ≤ 3 (violated).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = mk_real_int_const(&mut terms, 5);
    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let three = mk_real_int_const(&mut terms, 3);

    let le_5x = terms.mk_le(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real chain nonneg should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_chain_concrete_expr_negative() {
    // Real-sort chain with negative concrete endpoints as native ay Rational
    // constants.
    //
    // Bounds: ¬(-1 ≤ x), ¬(x ≤ -3) → chain: -1 ≤ x ≤ -3 → -1 ≤ -3 (violated).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let neg1 = mk_real_int_const(&mut terms, -1);
    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let neg3 = mk_real_int_const(&mut terms, -3);

    let le_n1_x = terms.mk_le(neg1, x);
    let le_x_n3 = terms.mk_le(x, neg3);
    let not_le_n1_x = terms.mk_not(le_n1_x);
    let not_le_x_n3 = terms.mk_not(le_x_n3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_n1_x, not_le_x_n3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real chain negative should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_chain_concrete_expr_lt() {
    // Real-sort chain with strict inequality and concrete endpoints.
    // Bounds: ¬(5 < x), ¬(x ≤ 3) → chain: 5 < x ≤ 3 → 5 < 3 (violated).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = mk_real_int_const(&mut terms, 5);
    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let three = mk_real_int_const(&mut terms, 3);

    let lt_5x = terms.mk_lt(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_lt_5x = terms.mk_not(lt_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real chain Lt should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_chain_concrete_expr_mixed_sign_normalizes_ofnat() {
    // Mixed positive/negative endpoints: the chain builder normalizes both
    // endpoint forms before closing.
    //
    // Bounds: ¬(3 ≤ x), ¬(x ≤ -1) → chain: 3 ≤ x ≤ -1 → contradiction.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = mk_real_int_const(&mut terms, 3);
    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let neg1 = mk_real_int_const(&mut terms, -1);

    let le_3_x = terms.mk_le(three, x);
    let le_x_neg1 = terms.mk_le(x, neg1);
    let not_le_3_x = terms.mk_not(le_3_x);
    let not_le_x_neg1 = terms.mk_not(le_x_neg1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_x, not_le_x_neg1], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real chain mixed sign should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}
