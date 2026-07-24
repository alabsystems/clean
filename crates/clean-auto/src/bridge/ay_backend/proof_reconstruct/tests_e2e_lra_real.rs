// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end Real-sort LRA Farkas proof reconstruction tests with kernel
//! TypeChecker validation.
//!
//! Split from the unweighted `tests_e2e_lra` module for file-size compliance.
//! Part of #2422 (Phase D: replace sorryAx with real arithmetic proofs).

use super::tests_e2e_lra::{
    mk_le_real, mk_lt_real, mk_real_add_expr, mk_real_int_const_expr, mk_real_ofint_expr,
    mk_real_ofnat,
};
use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{FarkasAnnotation, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

fn mk_real_lra_symbolic_additive_closeout_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let four_real = mk_real_ofnat(4);
    let one_real = mk_real_ofnat(1);
    let two_real = mk_real_ofnat(2);
    let test_x = mk_real_ofint_expr(&Expr::const_(Name::from_string("testXI"), vec![]));
    let test_y = mk_real_ofint_expr(&Expr::const_(Name::from_string("testYI"), vec![]));

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_four = terms.mk_var("const4", Sort::Real);
    let ay_one = terms.mk_var("const1", Sort::Real);
    let ay_two = terms.mk_var("const2", Sort::Real);
    let ay_x = terms.mk_var("testX", Sort::Real);
    let ay_y = terms.mk_var("testY", Sort::Real);

    map.register_var("const4", four_real.clone(), real_ty.clone());
    map.register_var("const1", one_real.clone(), real_ty.clone());
    map.register_var("const2", two_real.clone(), real_ty.clone());
    map.register_var("testX", test_x.clone(), real_ty.clone());
    map.register_var("testY", test_y.clone(), real_ty.clone());

    let ay_x_plus_y = terms.mk_add(vec![ay_x, ay_y]);
    let le_4_xy = terms.mk_le(ay_four, ay_x_plus_y);
    let le_x_1 = terms.mk_le(ay_x, ay_one);
    let le_y_2 = terms.mk_le(ay_y, ay_two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1 = terms.mk_not(le_x_1);
    let not_le_y_2 = terms.mk_not(le_y_2);

    let le_4_xy_prop = mk_le_real(&four_real, &mk_real_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_real(&test_x, &one_real);
    let le_y_2_prop = mk_le_real(&test_y, &two_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2", h3_id, Expr::fvar(h3_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_4_xy, not_le_x_1, not_le_y_2],
        farkas,
    );
    let s1 = proof.add_assume(le_4_xy, None);
    let s2 = proof.add_resolution(vec![not_le_x_1, not_le_y_2], not_le_4_xy, s0, s1);
    let s3 = proof.add_assume(le_x_1, None);
    let s4 = proof.add_resolution(vec![not_le_y_2], not_le_x_1, s2, s3);
    let s5 = proof.add_assume(le_y_2, None);
    proof.add_resolution(vec![], not_le_y_2, s4, s5);

    let hyps = vec![
        (h1_id, "h_4_le_xy", le_4_xy_prop),
        (h2_id, "h_x_le_1", le_x_1_prop),
        (h3_id, "h_y_le_2", le_y_2_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_real_lra_symbolic_additive_closeout_type_checks() {
    let (terms, map, proof, _hyps) = mk_real_lra_symbolic_additive_closeout_ay_proof();
    let neg_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

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

/// Build ay terms, variable mappings, and a Real-sort LRA Farkas proof with
/// non-chaining concrete bounds: 3 ≤ 2, 5 ≤ 4.
fn mk_real_lra_additive_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let three_real = mk_real_ofnat(3);
    let two_real = mk_real_ofnat(2);
    let five_real = mk_real_ofnat(5);
    let four_real = mk_real_ofnat(4);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Real);
    let ay_two = terms.mk_var("const2", Sort::Real);
    let ay_five = terms.mk_var("const5", Sort::Real);
    let ay_four = terms.mk_var("const4", Sort::Real);

    map.register_var("const3", three_real.clone(), real_ty.clone());
    map.register_var("const2", two_real.clone(), real_ty.clone());
    map.register_var("const5", five_real.clone(), real_ty.clone());
    map.register_var("const4", four_real.clone(), real_ty.clone());

    let le_3_2 = terms.mk_le(ay_three, ay_two);
    let le_5_4 = terms.mk_le(ay_five, ay_four);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);

    let le_3_2_prop = mk_le_real(&three_real, &two_real);
    let le_5_4_prop = mk_le_real(&five_real, &four_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_3_le_2", h1_id, Expr::fvar(h1_id), le_3_2_prop.clone());
    map.register_hypothesis("h_5_le_4", h2_id, Expr::fvar(h2_id), le_5_4_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4], farkas);
    let s1 = proof.add_assume(le_3_2, None);
    let s2 = proof.add_resolution(vec![not_le_5_4], not_le_3_2, s0, s1);
    let s3 = proof.add_assume(le_5_4, None);
    proof.add_resolution(vec![], not_le_5_4, s2, s3);

    let hyps = vec![
        (h1_id, "h_3_le_2", le_3_2_prop),
        (h2_id, "h_5_le_4", le_5_4_prop),
    ];
    (terms, map, proof, hyps)
}

/// Build ay terms, variable mappings, and a Real-sort LRA Farkas proof with
/// mixed endpoint forms: 3 ≤ -1, -2 < 0.
fn mk_real_lra_additive_mixed_sign_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let three_real = mk_real_int_const_expr(3);
    let neg1_real = mk_real_int_const_expr(-1);
    let neg2_real = mk_real_int_const_expr(-2);
    let zero_real = mk_real_int_const_expr(0);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Real);
    let ay_neg1 = terms.mk_var("constNeg1", Sort::Real);
    let ay_neg2 = terms.mk_var("constNeg2", Sort::Real);
    let ay_zero = terms.mk_var("const0", Sort::Real);

    map.register_var("const3", three_real.clone(), real_ty.clone());
    map.register_var("constNeg1", neg1_real.clone(), real_ty.clone());
    map.register_var("constNeg2", neg2_real.clone(), real_ty.clone());
    map.register_var("const0", zero_real.clone(), real_ty.clone());

    let le_3_neg1 = terms.mk_le(ay_three, ay_neg1);
    let lt_neg2_0 = terms.mk_lt(ay_neg2, ay_zero);
    let not_le_3_neg1 = terms.mk_not(le_3_neg1);
    let not_lt_neg2_0 = terms.mk_not(lt_neg2_0);

    let le_3_neg1_prop = mk_le_real(&three_real, &neg1_real);
    let lt_neg2_0_prop = mk_lt_real(&neg2_real, &zero_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis(
        "h_3_le_neg1",
        h1_id,
        Expr::fvar(h1_id),
        le_3_neg1_prop.clone(),
    );
    map.register_hypothesis(
        "h_neg2_lt_0",
        h2_id,
        Expr::fvar(h2_id),
        lt_neg2_0_prop.clone(),
    );

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_neg1, not_lt_neg2_0], farkas);
    let s1 = proof.add_assume(le_3_neg1, None);
    let s2 = proof.add_resolution(vec![not_lt_neg2_0], not_le_3_neg1, s0, s1);
    let s3 = proof.add_assume(lt_neg2_0, None);
    proof.add_resolution(vec![], not_lt_neg2_0, s2, s3);

    let hyps = vec![
        (h1_id, "h_3_le_neg1", le_3_neg1_prop),
        (h2_id, "h_neg2_lt_0", lt_neg2_0_prop),
    ];
    (terms, map, proof, hyps)
}

/// E2E: Real-sort additive LRA path with concrete non-chaining bounds
/// type-checks to False after downcasting through the Int additive closer.
#[test]
fn test_e2e_real_lra_additive_non_chaining_type_checks() {
    let (terms, map, proof, _hyps) = mk_real_lra_additive_ay_proof();
    let neg_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

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

/// E2E: Real-sort additive LRA path with mixed `Real.ofNat` and
/// `Real.ofInt (Int.negSucc ..)` endpoints type-checks to False.
#[test]
fn test_e2e_real_lra_additive_mixed_sign_type_checks() {
    let (terms, map, proof, _hyps) = mk_real_lra_additive_mixed_sign_ay_proof();
    let neg_goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

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
