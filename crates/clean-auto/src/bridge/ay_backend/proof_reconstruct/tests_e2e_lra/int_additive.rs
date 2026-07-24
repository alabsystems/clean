// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int-additive LRA e2e coverage.

use super::support::{
    add_three_literal_farkas_resolution, mk_int_add_expr, mk_int_ofnat, mk_le_int,
    negated_false_goal, LraHypothesisSetup,
};
use super::*;

/// Build ay terms, variable mappings, and LRA Farkas proof with non-chaining
/// concrete bounds: 5 ≤ 2, 4 ≤ 1.
fn mk_lra_additive_ay_proof() -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five_int = mk_int_ofnat(5);
    let two_int = mk_int_ofnat(2);
    let four_int = mk_int_ofnat(4);
    let one_int = mk_int_ofnat(1);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_one = terms.mk_var("const1", Sort::Int);

    map.register_var("const5", five_int.clone(), int_ty.clone());
    map.register_var("const2", two_int.clone(), int_ty.clone());
    map.register_var("const4", four_int.clone(), int_ty.clone());
    map.register_var("const1", one_int.clone(), int_ty.clone());

    let le_5_2 = terms.mk_le(ay_five, ay_two);
    let le_4_1 = terms.mk_le(ay_four, ay_one);
    let not_le_5_2 = terms.mk_not(le_5_2);
    let not_le_4_1 = terms.mk_not(le_4_1);

    let le_5_2_prop = mk_le_int(&five_int, &two_int);
    let le_4_1_prop = mk_le_int(&four_int, &one_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);

    map.register_hypothesis("h_5_le_2", h1_id, Expr::fvar(h1_id), le_5_2_prop.clone());
    map.register_hypothesis("h_4_le_1", h2_id, Expr::fvar(h2_id), le_4_1_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_2, not_le_4_1], farkas);
    let s1 = proof.add_assume(le_5_2, None);
    let s2 = proof.add_resolution(vec![not_le_4_1], not_le_5_2, s0, s1);
    let s3 = proof.add_assume(le_4_1, None);
    proof.add_resolution(vec![], not_le_4_1, s2, s3);

    let hyps = vec![
        (h1_id, "h_5_le_2", le_5_2_prop),
        (h2_id, "h_4_le_1", le_4_1_prop),
    ];
    (terms, map, proof, hyps)
}

/// E2E: LRA Farkas additive path with non-chaining concrete bounds.
#[test]
fn test_e2e_lra_additive_non_chaining_type_checks() {
    let (terms, map, proof, _hyps) = mk_lra_additive_ay_proof();
    let neg_goal = negated_false_goal();
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
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

fn mk_lra_symbolic_additive_closeout_ay_proof(
) -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let four_int = mk_int_ofnat(4);
    let one_int = mk_int_ofnat(1);
    let two_int = mk_int_ofnat(2);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_one = terms.mk_var("const1", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const4", four_int.clone(), int_ty.clone());
    map.register_var("const1", one_int.clone(), int_ty.clone());
    map.register_var("const2", two_int.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty.clone());

    let ay_x_plus_y = terms.mk_add(vec![ay_x, ay_y]);
    let le_4_xy = terms.mk_le(ay_four, ay_x_plus_y);
    let le_x_1 = terms.mk_le(ay_x, ay_one);
    let le_y_2 = terms.mk_le(ay_y, ay_two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1 = terms.mk_not(le_x_1);
    let not_le_y_2 = terms.mk_not(le_y_2);

    let le_4_xy_prop = mk_le_int(&four_int, &mk_int_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_int(&test_x, &one_int);
    let le_y_2_prop = mk_le_int(&test_y, &two_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2", h3_id, Expr::fvar(h3_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    add_three_literal_farkas_resolution(
        &mut proof,
        [not_le_4_xy, not_le_x_1, not_le_y_2],
        [le_4_xy, le_x_1, le_y_2],
    );

    let hyps = vec![
        (h1_id, "h_4_le_xy", le_4_xy_prop),
        (h2_id, "h_x_le_1", le_x_1_prop),
        (h3_id, "h_y_le_2", le_y_2_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_lra_symbolic_additive_closeout_type_checks() {
    let (terms, map, proof, _hyps) = mk_lra_symbolic_additive_closeout_ay_proof();
    let neg_goal = negated_false_goal();
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
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

fn mk_lra_symbolic_additive_subset_ay_proof(
) -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let three_int = mk_int_ofnat(3);
    let two_int = mk_int_ofnat(2);
    let zero_int = mk_int_ofnat(0);
    let ten_int = mk_int_ofnat(10);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_zero = terms.mk_var("const0", Sort::Int);
    let ay_ten = terms.mk_var("const10", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const3", three_int.clone(), int_ty.clone());
    map.register_var("const2", two_int.clone(), int_ty.clone());
    map.register_var("const0", zero_int.clone(), int_ty.clone());
    map.register_var("const10", ten_int.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty.clone());

    let ay_x_plus_3 = terms.mk_add(vec![ay_x, ay_three]);
    let ay_y_plus_2 = terms.mk_add(vec![ay_y, ay_two]);
    let le_x3_y = terms.mk_le(ay_x_plus_3, ay_y);
    let le_y2_x = terms.mk_le(ay_y_plus_2, ay_x);
    let le_0_10 = terms.mk_le(ay_zero, ay_ten);
    let not_le_x3_y = terms.mk_not(le_x3_y);
    let not_le_y2_x = terms.mk_not(le_y2_x);
    let not_le_0_10 = terms.mk_not(le_0_10);

    let le_x3_y_prop = mk_le_int(&mk_int_add_expr(&test_x, &three_int), &test_y);
    let le_y2_x_prop = mk_le_int(&mk_int_add_expr(&test_y, &two_int), &test_x);
    let le_0_10_prop = mk_le_int(&zero_int, &ten_int);

    let h1_id = FVarId::new(20);
    let h2_id = FVarId::new(21);
    let h3_id = FVarId::new(22);
    map.register_hypothesis("h_x3_le_y", h1_id, Expr::fvar(h1_id), le_x3_y_prop.clone());
    map.register_hypothesis("h_y2_le_x", h2_id, Expr::fvar(h2_id), le_y2_x_prop.clone());
    map.register_hypothesis("h_0_le_10", h3_id, Expr::fvar(h3_id), le_0_10_prop.clone());

    let mut proof = Proof::new();
    add_three_literal_farkas_resolution(
        &mut proof,
        [not_le_x3_y, not_le_y2_x, not_le_0_10],
        [le_x3_y, le_y2_x, le_0_10],
    );

    let hyps = vec![
        (h1_id, "h_x3_le_y", le_x3_y_prop),
        (h2_id, "h_y2_le_x", le_y2_x_prop),
        (h3_id, "h_0_le_10", le_0_10_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_lra_symbolic_additive_subset_type_checks() {
    let (terms, map, proof, _hyps) = mk_lra_symbolic_additive_subset_ay_proof();
    let neg_goal = negated_false_goal();
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
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
