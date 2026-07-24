// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2e tests for raw `>` and `>=` operator normalization.
//!
//! ay's `decompose_arithmetic_eq` / `decompose_disequality` produce raw
//! `Symbol::Named(">"/">=")` terms. `term_translate.rs` normalizes these
//! to `<`/`<=` with swapped arguments.

use super::support::*;
use super::*;

fn mk_lra_raw_gt_normalization_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let three = mk_int_ofnat(3);
    let three_b = mk_int_ofnat(3);
    let four = mk_int_ofnat(4);
    let five = mk_int_ofnat(5);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_three_b = terms.mk_var("const3b", Sort::Int);
    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_five = terms.mk_var("const5", Sort::Int);

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("const3b", three_b.clone(), int_ty.clone());
    map.register_var("const4", four.clone(), int_ty.clone());
    map.register_var("const5", five.clone(), int_ty);

    let gt_3_3 = terms.mk_app(
        Symbol::Named(">".to_string()),
        vec![ay_three, ay_three_b],
        Sort::Bool,
    );
    let gt_4_5 = terms.mk_app(
        Symbol::Named(">".to_string()),
        vec![ay_four, ay_five],
        Sort::Bool,
    );
    let not_gt_3_3 = terms.mk_not(gt_3_3);
    let not_gt_4_5 = terms.mk_not(gt_4_5);

    // Raw `>` normalizes to swapped `<` propositions.
    let lt_3_3_prop = mk_lt_int(&three, &three_b);
    let lt_5_4_prop = mk_lt_int(&five, &four);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_3_lt_3", h1_id, Expr::fvar(h1_id), lt_3_3_prop.clone());
    map.register_hypothesis("h_5_lt_4", h2_id, Expr::fvar(h2_id), lt_5_4_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_gt_3_3, not_gt_4_5], farkas);
    let s1 = proof.add_assume(gt_3_3, None);
    let s2 = proof.add_resolution(vec![not_gt_4_5], not_gt_3_3, s0, s1);
    let s3 = proof.add_assume(gt_4_5, None);
    proof.add_resolution(vec![], not_gt_4_5, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_3_lt_3", lt_3_3_prop),
            (h2_id, "h_5_lt_4", lt_5_4_prop),
        ],
        context: "raw > normalization e2e",
    }
}

/// Build an e2e case with raw `>=` operator (as ay's decompose_arithmetic_eq
/// produces). `>=` normalizes to `<=` with swapped arguments, exercising the
/// Le closing path rather than the Lt path tested by `mk_lra_raw_gt_normalization_case`.
///
/// Bounds: not(2 >= 5) -> not(5 <= 2), not(1 >= 4) -> not(4 <= 1).
/// Both are individually violated concrete Le bounds (5 > 2, 4 > 1).
///
/// Part of #302 (proof coverage: raw >= normalization through TypeChecker).
fn mk_lra_raw_ge_normalization_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let two = mk_int_ofnat(2);
    let five = mk_int_ofnat(5);
    let one = mk_int_ofnat(1);
    let four = mk_int_ofnat(4);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_one = terms.mk_var("const1", Sort::Int);
    let ay_four = terms.mk_var("const4", Sort::Int);

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("const2", two.clone(), int_ty.clone());
    map.register_var("const5", five.clone(), int_ty.clone());
    map.register_var("const1", one.clone(), int_ty.clone());
    map.register_var("const4", four.clone(), int_ty);

    // Raw >= terms: mk_app bypasses normalization, matching ay preprocessing.
    let ge_2_5 = terms.mk_app(
        Symbol::Named(">=".to_string()),
        vec![ay_two, ay_five],
        Sort::Bool,
    );
    let ge_1_4 = terms.mk_app(
        Symbol::Named(">=".to_string()),
        vec![ay_one, ay_four],
        Sort::Bool,
    );
    let not_ge_2_5 = terms.mk_not(ge_2_5);
    let not_ge_1_4 = terms.mk_not(ge_1_4);

    // Raw >= normalizes to swapped <=: 2 >= 5 -> 5 <= 2, 1 >= 4 -> 4 <= 1.
    let le_5_2_prop = mk_le_int(&five, &two);
    let le_4_1_prop = mk_le_int(&four, &one);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_5_le_2", h1_id, Expr::fvar(h1_id), le_5_2_prop.clone());
    map.register_hypothesis("h_4_le_1", h2_id, Expr::fvar(h2_id), le_4_1_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_ge_2_5, not_ge_1_4], farkas);
    let s1 = proof.add_assume(ge_2_5, None);
    let s2 = proof.add_resolution(vec![not_ge_1_4], not_ge_2_5, s0, s1);
    let s3 = proof.add_assume(ge_1_4, None);
    proof.add_resolution(vec![], not_ge_1_4, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_2", le_5_2_prop),
            (h2_id, "h_4_le_1", le_4_1_prop),
        ],
        context: "raw >= normalization e2e",
    }
}

#[test]
fn test_e2e_lra_raw_gt_normalization_type_checks() {
    let case = mk_lra_raw_gt_normalization_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}

#[test]
fn test_e2e_lra_raw_ge_normalization_type_checks() {
    let case = mk_lra_raw_ge_normalization_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}
