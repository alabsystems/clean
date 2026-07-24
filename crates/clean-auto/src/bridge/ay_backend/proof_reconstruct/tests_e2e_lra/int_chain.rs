// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int-chain LRA e2e coverage.

use super::support::{mk_int_ofnat, mk_le_int, negated_false_goal, LraHypothesisSetup};
use super::*;

/// Build ay terms, variable mappings, and LRA Farkas proof: 5 ≤ x, x ≤ 3.
fn mk_lra_farkas_ay_proof() -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five_int = mk_int_ofnat(5);
    let three_int = mk_int_ofnat(3);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);

    map.register_var("const5", five_int.clone(), int_ty.clone());
    map.register_var("const3", three_int.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());

    let le_5x = terms.mk_le(ay_five, ay_x);
    let le_x3 = terms.mk_le(ay_x, ay_three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let le_5x_prop = mk_le_int(&five_int, &test_x);
    let le_x3_prop = mk_le_int(&test_x, &three_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_5_le_x", h1_id, Expr::fvar(h1_id), le_5x_prop.clone());
    map.register_hypothesis("h_x_le_3", h2_id, Expr::fvar(h2_id), le_x3_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);
    let s1 = proof.add_assume(le_5x, None);
    let s2 = proof.add_resolution(vec![not_le_x3], not_le_5x, s0, s1);
    let s3 = proof.add_assume(le_x3, None);
    proof.add_resolution(vec![], not_le_x3, s2, s3);

    let hyps = vec![
        (h1_id, "h_5_le_x", le_5x_prop),
        (h2_id, "h_x_le_3", le_x3_prop),
    ];
    (terms, map, proof, hyps)
}

/// E2E: LRA Farkas le_trans chain with ay-variable-mapped concrete endpoints.
#[test]
fn test_e2e_lra_farkas_le_trans_closes_via_expr_concrete_fallback() {
    let (terms, map, proof, _hyps) = mk_lra_farkas_ay_proof();
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

/// Build ay terms, variable mappings, and 3-bound LRA Farkas proof:
/// 5 ≤ x, x ≤ y, y ≤ 3.
fn mk_lra_farkas_3bound_ay_proof() -> (TermStore, VariableMapping, Proof, LraHypothesisSetup) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five_int = mk_int_ofnat(5);
    let three_int = mk_int_ofnat(3);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const5", five_int.clone(), int_ty.clone());
    map.register_var("const3", three_int.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty.clone());

    let le_5x = terms.mk_le(ay_five, ay_x);
    let le_xy = terms.mk_le(ay_x, ay_y);
    let le_y3 = terms.mk_le(ay_y, ay_three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_xy = terms.mk_not(le_xy);
    let not_le_y3 = terms.mk_not(le_y3);

    let le_5x_prop = mk_le_int(&five_int, &test_x);
    let le_xy_prop = mk_le_int(&test_x, &test_y);
    let le_y3_prop = mk_le_int(&test_y, &three_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);

    map.register_hypothesis("h_5_le_x", h1_id, Expr::fvar(h1_id), le_5x_prop.clone());
    map.register_hypothesis("h_x_le_y", h2_id, Expr::fvar(h2_id), le_xy_prop.clone());
    map.register_hypothesis("h_y_le_3", h3_id, Expr::fvar(h3_id), le_y3_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 =
        proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_xy, not_le_y3], farkas);
    let s1 = proof.add_assume(le_5x, None);
    let s2 = proof.add_resolution(vec![not_le_xy, not_le_y3], not_le_5x, s0, s1);
    let s3 = proof.add_assume(le_xy, None);
    let s4 = proof.add_resolution(vec![not_le_y3], not_le_xy, s2, s3);
    let s5 = proof.add_assume(le_y3, None);
    proof.add_resolution(vec![], not_le_y3, s4, s5);

    let hyps = vec![
        (h1_id, "h_5_le_x", le_5x_prop),
        (h2_id, "h_x_le_y", le_xy_prop),
        (h3_id, "h_y_le_3", le_y3_prop),
    ];
    (terms, map, proof, hyps)
}

/// E2E: 3-bound LRA Farkas chain (5 ≤ x, x ≤ y, y ≤ 3) closes via
/// kernel-Expr concrete fallback.
#[test]
fn test_e2e_lra_farkas_three_bound_le_chain_closes_via_expr_concrete_fallback() {
    let (terms, map, proof, _hyps) = mk_lra_farkas_3bound_ay_proof();
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
