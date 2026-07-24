// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int-additive LRA e2e NF coverage.

use super::support::{
    mk_int_add_expr, mk_int_ofnat, mk_le_int, negated_false_goal, LraHypothesisSetup,
};
use super::*;

fn add_four_literal_farkas_resolution(
    proof: &mut Proof,
    clause: [ay_core::TermId; 4],
    assumptions: [ay_core::TermId; 4],
) {
    let [not_a, not_b, not_c, not_d] = clause;
    let [a, b, c, d] = assumptions;
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_a, not_b, not_c, not_d], farkas);
    let s1 = proof.add_assume(a, None);
    let s2 = proof.add_resolution(vec![not_b, not_c, not_d], not_a, s0, s1);
    let s3 = proof.add_assume(b, None);
    let s4 = proof.add_resolution(vec![not_c, not_d], not_b, s2, s3);
    let s5 = proof.add_assume(c, None);
    let s6 = proof.add_resolution(vec![not_d], not_c, s4, s5);
    let s7 = proof.add_assume(d, None);
    proof.add_resolution(vec![], not_d, s6, s7);
}

fn mk_lra_4bound_additive_nf_full_cancellation_ay_proof(
) -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five_int = mk_int_ofnat(5);
    let three_int = mk_int_ofnat(3);
    let two_int = mk_int_ofnat(2);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);
    let test_z = Expr::const_(Name::from_string("testZ"), vec![]);
    let test_w = Expr::const_(Name::from_string("testW"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);
    let ay_z = terms.mk_var("testZ", Sort::Int);
    let ay_w = terms.mk_var("testW", Sort::Int);

    map.register_var("const5", five_int.clone(), int_ty.clone());
    map.register_var("const3", three_int.clone(), int_ty.clone());
    map.register_var("const2", two_int.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty.clone());
    map.register_var("testZ", test_z.clone(), int_ty.clone());
    map.register_var("testW", test_w.clone(), int_ty.clone());

    let ay_x_plus_5 = terms.mk_add(vec![ay_x, ay_five]);
    let ay_y_plus_3 = terms.mk_add(vec![ay_y, ay_three]);
    let ay_z_plus_2 = terms.mk_add(vec![ay_z, ay_two]);
    let le_x5_y = terms.mk_le(ay_x_plus_5, ay_y);
    let le_y3_z = terms.mk_le(ay_y_plus_3, ay_z);
    let le_z2_w = terms.mk_le(ay_z_plus_2, ay_w);
    let le_w_x = terms.mk_le(ay_w, ay_x);
    let not_le_x5_y = terms.mk_not(le_x5_y);
    let not_le_y3_z = terms.mk_not(le_y3_z);
    let not_le_z2_w = terms.mk_not(le_z2_w);
    let not_le_w_x = terms.mk_not(le_w_x);

    let le_x5_y_prop = mk_le_int(&mk_int_add_expr(&test_x, &five_int), &test_y);
    let le_y3_z_prop = mk_le_int(&mk_int_add_expr(&test_y, &three_int), &test_z);
    let le_z2_w_prop = mk_le_int(&mk_int_add_expr(&test_z, &two_int), &test_w);
    let le_w_x_prop = mk_le_int(&test_w, &test_x);

    let h1_id = FVarId::new(30);
    let h2_id = FVarId::new(31);
    let h3_id = FVarId::new(32);
    let h4_id = FVarId::new(33);
    map.register_hypothesis("h_x5_le_y", h1_id, Expr::fvar(h1_id), le_x5_y_prop.clone());
    map.register_hypothesis("h_y3_le_z", h2_id, Expr::fvar(h2_id), le_y3_z_prop.clone());
    map.register_hypothesis("h_z2_le_w", h3_id, Expr::fvar(h3_id), le_z2_w_prop.clone());
    map.register_hypothesis("h_w_le_x", h4_id, Expr::fvar(h4_id), le_w_x_prop.clone());

    let mut proof = Proof::new();
    add_four_literal_farkas_resolution(
        &mut proof,
        [not_le_x5_y, not_le_y3_z, not_le_z2_w, not_le_w_x],
        [le_x5_y, le_y3_z, le_z2_w, le_w_x],
    );

    let hyps = vec![
        (h1_id, "h_x5_le_y", le_x5_y_prop),
        (h2_id, "h_y3_le_z", le_y3_z_prop),
        (h3_id, "h_z2_le_w", le_z2_w_prop),
        (h4_id, "h_w_le_x", le_w_x_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_lra_4bound_additive_nf_full_cancellation_type_checks() {
    let (terms, map, proof, _hyps) = mk_lra_4bound_additive_nf_full_cancellation_ay_proof();
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
