// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for N-bound additive Le/Lt reconstruction in LRA Farkas theory lemmas.

use super::support::boundary::assert_lra_trust_boundary;
use super::support::semantic::{mk_raw_le, mk_raw_lt, register_int_const};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, VariableMapping,
};

#[test]
fn test_theory_lemma_lra_farkas_int_additive_two_bound_le() {
    // Two Int Le bounds with concrete endpoints that don't chain but whose
    // additive combination is contradictory.
    // Bounds: ¬(3 ≤ 2), ¬(5 ≤ 4) — no shared ay term.
    // Chain path fails (no intermediate match).
    // Additive path: 3+5 = 8 > 6 = 2+4 → contradiction via Int.add_le_add_left.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let le_5_4 = mk_raw_le(&mut terms, five, four);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "additive Le reconstruction should succeed with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_non_unit_coefficients_reconstructed() {
    // The unscaled additive proof (Int.add_le_add_left + le_trans) is sound
    // independently of the Farkas coefficients: it derives (lhs0+lhs1) ≤
    // (rhs0+rhs1) from the two hypotheses. Non-unit coefficients are ay's
    // certification metadata; the kernel proof does not use them.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let le_5_4 = mk_raw_le(&mut terms, five, four);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "non-unit coefficient additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_asymmetric_coefficients_reconstructed() {
    // Asymmetric non-unit coefficients [3, 1] with concrete non-chaining bounds.
    // The unscaled additive sum (7+5=12 > 4+2=6) is contradictory independently
    // of the Farkas certificate, so reconstruction succeeds.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let seven = register_int_const(&mut terms, &mut map, "const7", 7);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);

    let le_7_4 = mk_raw_le(&mut terms, seven, four);
    let le_5_2 = mk_raw_le(&mut terms, five, two);
    let not_le_7_4 = terms.mk_not(le_7_4);
    let not_le_5_2 = terms.mk_not(le_5_2);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[3, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_7_4, not_le_5_2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "asymmetric coefficient additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_non_contradictory_trust_boundary() {
    // Two Int Le bounds with concrete endpoints where the additive sum
    // is NOT contradictory → should hit trust boundary.
    // Bounds: ¬(1 ≤ 3), ¬(2 ≤ 4) → 1+2=3 ≤ 7=3+4 (not violated)
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let one = register_int_const(&mut terms, &mut map, "const1", 1);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let le_1_3 = mk_raw_le(&mut terms, one, three);
    let le_2_4 = mk_raw_le(&mut terms, two, four);
    let not_le_1_3 = terms.mk_not(le_1_3);
    let not_le_2_4 = terms.mk_not(le_2_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_1_3, not_le_2_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_three_bound_le() {
    // Three Int Le bounds with concrete non-chaining endpoints whose additive
    // sum is contradictory: ¬(5≤2), ¬(4≤1), ¬(3≤0) → 5+4+3=12 > 3=2+1+0.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let one = register_int_const(&mut terms, &mut map, "const1", 1);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let zero = register_int_const(&mut terms, &mut map, "const0", 0);

    let le_5_2 = mk_raw_le(&mut terms, five, two);
    let le_4_1 = mk_raw_le(&mut terms, four, one);
    let le_3_0 = mk_raw_le(&mut terms, three, zero);
    let not_le_5_2 = terms.mk_not(le_5_2);
    let not_le_4_1 = terms.mk_not(le_4_1);
    let not_le_3_0 = terms.mk_not(le_3_0);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_2, not_le_4_1, not_le_3_0], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "three-bound additive Le reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_four_bound_le() {
    // Four Int Le bounds with concrete non-chaining endpoints.
    // ¬(3≤1), ¬(4≤2), ¬(5≤3), ¬(6≤1) → 3+4+5+6=18 > 7=1+2+3+1.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let c3 = register_int_const(&mut terms, &mut map, "c3", 3);
    let c1a = register_int_const(&mut terms, &mut map, "c1a", 1);
    let c4 = register_int_const(&mut terms, &mut map, "c4", 4);
    let c2 = register_int_const(&mut terms, &mut map, "c2", 2);
    let c5 = register_int_const(&mut terms, &mut map, "c5", 5);
    let c3b = register_int_const(&mut terms, &mut map, "c3b", 3);
    let c6 = register_int_const(&mut terms, &mut map, "c6", 6);
    let c1b = register_int_const(&mut terms, &mut map, "c1b", 1);

    let le_3_1 = mk_raw_le(&mut terms, c3, c1a);
    let le_4_2 = mk_raw_le(&mut terms, c4, c2);
    let le_5_3 = mk_raw_le(&mut terms, c5, c3b);
    let le_6_1 = mk_raw_le(&mut terms, c6, c1b);
    let not_le_3_1 = terms.mk_not(le_3_1);
    let not_le_4_2 = terms.mk_not(le_4_2);
    let not_le_5_3 = terms.mk_not(le_5_3);
    let not_le_6_1 = terms.mk_not(le_6_1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_3_1, not_le_4_2, not_le_5_3, not_le_6_1],
        farkas,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "four-bound additive Le reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_three_bound_non_contradictory_trust_boundary() {
    // Three Int Le bounds whose additive sum is NOT contradictory → trust boundary.
    // ¬(1≤5), ¬(2≤6), ¬(3≤7) → 1+2+3=6 ≤ 18=5+6+7
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let one = register_int_const(&mut terms, &mut map, "c1", 1);
    let five = register_int_const(&mut terms, &mut map, "c5", 5);
    let two = register_int_const(&mut terms, &mut map, "c2", 2);
    let six = register_int_const(&mut terms, &mut map, "c6", 6);
    let three = register_int_const(&mut terms, &mut map, "c3", 3);
    let seven = register_int_const(&mut terms, &mut map, "c7", 7);

    let le_1_5 = mk_raw_le(&mut terms, one, five);
    let le_2_6 = mk_raw_le(&mut terms, two, six);
    let le_3_7 = mk_raw_le(&mut terms, three, seven);
    let not_le_1_5 = terms.mk_not(le_1_5);
    let not_le_2_6 = terms.mk_not(le_2_6);
    let not_le_3_7 = terms.mk_not(le_3_7);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_1_5, not_le_2_6, not_le_3_7], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

// =========================================================================
// Mixed Le/Lt additive combination tests (#302)
// =========================================================================

#[test]
fn test_theory_lemma_lra_farkas_int_additive_mixed_le_lt_two_bound() {
    // Mixed Le+Lt 2-bound additive combination.
    // Bounds: ¬(3 ≤ 2), ¬(5 < 4) — no shared ay term.
    // Combined op: Lt (any strict makes result strict).
    // Additive: 3+5=8 ≥ 2+4=6 → contradiction for Lt (sum_lhs >= sum_rhs).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let lt_5_4 = mk_raw_lt(&mut terms, five, four);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_lt_5_4 = terms.mk_not(lt_5_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_lt_5_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "mixed Le+Lt additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_all_lt_two_bound() {
    // All-Lt 2-bound additive combination.
    // Bounds: ¬(3 < 3), ¬(5 < 4) — both strict.
    // Combined op: Lt.
    // Additive: 3+5=8 ≥ 3+4=7 → contradiction for Lt.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let three_b = register_int_const(&mut terms, &mut map, "const3b", 3);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let lt_3_3 = mk_raw_lt(&mut terms, three, three_b);
    let lt_5_4 = mk_raw_lt(&mut terms, five, four);
    let not_lt_3_3 = terms.mk_not(lt_3_3);
    let not_lt_5_4 = terms.mk_not(lt_5_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_3_3, not_lt_5_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "all-Lt additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_mixed_three_bound_le_lt() {
    // Three-bound mixed Le+Lt additive combination.
    // Bounds: ¬(5≤2), ¬(4<1), ¬(3≤0) — one Lt among Le.
    // Combined op: Lt.
    // Additive: 5+4+3=12 ≥ 2+1+0=3 → contradiction for Lt.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "c5", 5);
    let two = register_int_const(&mut terms, &mut map, "c2", 2);
    let four = register_int_const(&mut terms, &mut map, "c4", 4);
    let one = register_int_const(&mut terms, &mut map, "c1", 1);
    let three = register_int_const(&mut terms, &mut map, "c3", 3);
    let zero = register_int_const(&mut terms, &mut map, "c0", 0);

    let le_5_2 = mk_raw_le(&mut terms, five, two);
    let lt_4_1 = mk_raw_lt(&mut terms, four, one);
    let le_3_0 = mk_raw_le(&mut terms, three, zero);
    let not_le_5_2 = terms.mk_not(le_5_2);
    let not_lt_4_1 = terms.mk_not(lt_4_1);
    let not_le_3_0 = terms.mk_not(le_3_0);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_2, not_lt_4_1, not_le_3_0], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "mixed three-bound Le+Lt additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_additive_lt_equal_sums_contradictory() {
    // Edge case: Lt combined op with equal sums. For Lt, sum_lhs >= sum_rhs is
    // contradictory (strict inequality can't hold when sums are equal).
    // Bounds: ¬(3 < 3), ¬(2 ≤ 2) — sums: 3+2=5 >= 3+2=5.
    // With all-Le this would NOT be contradictory (5 ≤ 5 is fine).
    // But with Lt combined op, 5 < 5 is violated.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "c3", 3);
    let three_b = register_int_const(&mut terms, &mut map, "c3b", 3);
    let two = register_int_const(&mut terms, &mut map, "c2", 2);
    let two_b = register_int_const(&mut terms, &mut map, "c2b", 2);

    let lt_3_3 = mk_raw_lt(&mut terms, three, three_b);
    let le_2_2 = mk_raw_le(&mut terms, two, two_b);
    let not_lt_3_3 = terms.mk_not(lt_3_3);
    let not_le_2_2 = terms.mk_not(le_2_2);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_3_3, not_le_2_2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Lt equal-sums additive reconstruction should succeed: {:?}",
        result.stats.first_diagnostic
    );
}
