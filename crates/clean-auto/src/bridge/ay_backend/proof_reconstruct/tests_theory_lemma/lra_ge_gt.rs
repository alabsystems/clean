// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `>=` / `>` operator normalization in LRA Farkas bound parsing.
//!
//! ay's `decompose_arithmetic_eq` and `decompose_disequality` create raw
//! `Symbol::Named(">="|">")` terms via `mk_app`, bypassing the normalizing
//! `mk_ge`/`mk_gt`. `parse_bound` must handle these by swapping arguments
//! to normalize them to the `<=`/`<` representation the reconstruction
//! pipeline expects.
//!
//! Part of #302: proof reconstruction trust boundary reduction.

use super::support::semantic::{mk_raw_ge, mk_raw_gt, mk_raw_le, register_int_const};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, VariableMapping,
};

#[test]
fn test_theory_lemma_lra_farkas_ge_normalized_to_le_additive() {
    // Two bounds using raw >= operator (as ay's decompose_arithmetic_eq produces).
    // ¬(2 >= 3) normalizes to ¬(3 <= 2); ¬(4 >= 5) normalizes to ¬(5 <= 4).
    // Additive: 3+5=8 > 6=2+4 → contradiction.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let two = register_int_const(&mut terms, &mut map, "c2", 2);
    let three = register_int_const(&mut terms, &mut map, "c3", 3);
    let four = register_int_const(&mut terms, &mut map, "c4", 4);
    let five = register_int_const(&mut terms, &mut map, "c5", 5);

    let ge_2_3 = mk_raw_ge(&mut terms, two, three);
    let ge_4_5 = mk_raw_ge(&mut terms, four, five);
    let not_ge_2_3 = terms.mk_not(ge_2_3);
    let not_ge_4_5 = terms.mk_not(ge_4_5);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_ge_2_3, not_ge_4_5], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "ge normalized to le additive should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_gt_normalized_to_lt_additive() {
    // Two bounds using raw > operator (as ay's decompose_disequality produces).
    // ¬(3 > 3) normalizes to ¬(3 < 3); ¬(4 > 5) normalizes to ¬(5 < 4).
    // Combined op: Lt. Additive: 3+5=8 >= 3+4=7 → contradiction for Lt.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "c3", 3);
    let three_b = register_int_const(&mut terms, &mut map, "c3b", 3);
    let four = register_int_const(&mut terms, &mut map, "c4", 4);
    let five = register_int_const(&mut terms, &mut map, "c5", 5);

    let gt_3_3 = mk_raw_gt(&mut terms, three, three_b);
    let gt_4_5 = mk_raw_gt(&mut terms, four, five);
    let not_gt_3_3 = terms.mk_not(gt_3_3);
    let not_gt_4_5 = terms.mk_not(gt_4_5);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_gt_3_3, not_gt_4_5], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "gt normalized to lt additive should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_mixed_ge_le_additive() {
    // Mix of normalized >= and standard <= in the same Farkas clause.
    // ¬(2 >= 5) normalizes to ¬(5 <= 2); ¬(4 <= 1) is standard.
    // Additive: 5+4=9 > 3=2+1 → contradiction.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let two = register_int_const(&mut terms, &mut map, "c2", 2);
    let five = register_int_const(&mut terms, &mut map, "c5", 5);
    let four = register_int_const(&mut terms, &mut map, "c4", 4);
    let one = register_int_const(&mut terms, &mut map, "c1", 1);

    let ge_2_5 = mk_raw_ge(&mut terms, two, five);
    let le_4_1 = mk_raw_le(&mut terms, four, one);
    let not_ge_2_5 = terms.mk_not(ge_2_5);
    let not_le_4_1 = terms.mk_not(le_4_1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_ge_2_5, not_le_4_1], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "mixed ge+le additive should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}
