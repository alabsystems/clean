// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-sort additive LRA Farkas tests (concrete, symbolic, and mixed).
//!
//! Split from `lra_real.rs` to respect the 500-line file limit.

use super::lra_real::{mk_le_real_prop, mk_real_add_expr, mk_real_ofint_expr, mk_real_ofnat_expr};
use super::support::boundary::assert_lra_boundary_description_starts_with;
use super::support::semantic::{mk_raw_le, mk_raw_lt, mk_real_int_const};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, Sort, TermStore, VariableMapping,
};
use clean_kernel::FVarId;

#[test]
fn test_theory_lemma_lra_farkas_real_symbolic_additive_alias_vars_hit_semantic_boundary() {
    // This fixture keeps all numeric endpoints behind ay Vars so the active
    // subset is no longer semantically equivalent to native ay arithmetic.
    // After semantic validation, it belongs in the trust-boundary bucket
    // instead of the Real additive success lane.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let four_real = mk_real_ofnat_expr(4);
    let one_real = mk_real_ofnat_expr(1);
    let two_real = mk_real_ofnat_expr(2);
    let test_x = mk_real_ofint_expr(&Expr::const_(Name::from_string("testXI"), vec![]));
    let test_y = mk_real_ofint_expr(&Expr::const_(Name::from_string("testYI"), vec![]));

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

    let le_4_xy_prop = mk_le_real_prop(&four_real, &mk_real_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_real_prop(&test_x, &one_real);
    let le_y_2_prop = mk_le_real_prop(&test_y, &two_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2", h3_id, Expr::fvar(h3_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_xy, not_le_x_1, not_le_y_2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_real_additive_two_bound_le_concrete() {
    // Real sort non-chaining 2-bound Le with concrete endpoints.
    // Bounds: ¬(3 ≤ 2), ¬(5 ≤ 4) — the first bound is already contradictory,
    // so reconstruction short-circuits before needing additive combination.
    let mut terms = TermStore::new();
    let map = VariableMapping::new();

    let three = mk_real_int_const(&mut terms, 3);
    let two = mk_real_int_const(&mut terms, 2);
    let five = mk_real_int_const(&mut terms, 5);
    let four = mk_real_int_const(&mut terms, 4);

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
        "Real concrete 2-bound Le should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_additive_negative_two_bound_le_concrete() {
    // Real sort non-chaining 2-bound Le with all-negative endpoints.
    // Bounds: ¬(-1 ≤ -2), ¬(-3 ≤ -5) → -4 > -7, so the additive sum is contradictory.
    // Uses the downcast-to-Int path: Real.ofInt_le_to_Int converts to Int
    // hypotheses, then Int additive closer.
    let mut terms = TermStore::new();
    let map = VariableMapping::new();

    let neg1 = mk_real_int_const(&mut terms, -1);
    let neg2 = mk_real_int_const(&mut terms, -2);
    let neg3 = mk_real_int_const(&mut terms, -3);
    let neg5 = mk_real_int_const(&mut terms, -5);

    let le_neg1_neg2 = mk_raw_le(&mut terms, neg1, neg2);
    let le_neg3_neg5 = mk_raw_le(&mut terms, neg3, neg5);
    let not_le_neg1_neg2 = terms.mk_not(le_neg1_neg2);
    let not_le_neg3_neg5 = terms.mk_not(le_neg3_neg5);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_neg1_neg2, not_le_neg3_neg5], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real negative 2-bound Le should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_additive_mixed_endpoint_forms_lt_concrete() {
    // Real sort mixed-form additive contradiction.
    // Bound 1 mixes `Real.ofNat` on the lhs with `Real.ofInt (Int.negSucc ..)` on the rhs.
    // Bound 2 flips that shape and uses Lt, forcing the additive path to normalize/downcast both
    // endpoint directions in one clause set.
    // Bounds: ¬(3 ≤ -1), ¬(-2 < 0) → 3 + (-2) = 1 >= -1 + 0 = -1, contradictory for Lt.
    let mut terms = TermStore::new();
    let map = VariableMapping::new();

    let three = mk_real_int_const(&mut terms, 3);
    let neg1 = mk_real_int_const(&mut terms, -1);
    let neg2 = mk_real_int_const(&mut terms, -2);
    let zero = mk_real_int_const(&mut terms, 0);

    let le_3_neg1 = mk_raw_le(&mut terms, three, neg1);
    let lt_neg2_0 = mk_raw_lt(&mut terms, neg2, zero);
    let not_le_3_neg1 = terms.mk_not(le_3_neg1);
    let not_lt_neg2_0 = terms.mk_not(lt_neg2_0);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_neg1, not_lt_neg2_0], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Real mixed-endpoint Lt should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_two_bound_mixed_alias_vars_hit_semantic_boundary() {
    // 2-bound Real unit-coefficient case: each bound has one symbolic endpoint
    // and one Lean-concrete endpoint, but the constants are still encoded as
    // ay Vars. That alias-var encoding is rejected by active-subset semantic
    // validation before additive normalization/cancellation can run.
    //   Bounds: ¬(x + 2 ≤ 3), ¬(4 ≤ x + 1)
    // If this shape should exercise the Real additive success lane, the
    // numeric endpoints must be native ay constants rather than alias vars.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);

    // Symbolic variable x → Real.ofInt(xI)
    let test_x = mk_real_ofint_expr(&Expr::const_(Name::from_string("xI"), vec![]));
    let ay_x = terms.mk_var("testX", Sort::Real);
    map.register_var("testX", test_x.clone(), real_ty.clone());

    // Concrete constants as ay vars: boundary-only after #2902.
    let (one_r, two_r, three_r, four_r) = (
        mk_real_ofnat_expr(1),
        mk_real_ofnat_expr(2),
        mk_real_ofnat_expr(3),
        mk_real_ofnat_expr(4),
    );
    let ay_one = terms.mk_var("const1", Sort::Real);
    let ay_two = terms.mk_var("const2", Sort::Real);
    let ay_three = terms.mk_var("const3", Sort::Real);
    let ay_four = terms.mk_var("const4", Sort::Real);
    map.register_var("const1", one_r.clone(), real_ty.clone());
    map.register_var("const2", two_r.clone(), real_ty.clone());
    map.register_var("const3", three_r.clone(), real_ty.clone());
    map.register_var("const4", four_r.clone(), real_ty.clone());

    // ay compound terms and bounds
    let ay_xp2 = terms.mk_add(vec![ay_x, ay_two]);
    let ay_xp1 = terms.mk_add(vec![ay_x, ay_one]);
    let le_xp2_3 = terms.mk_le(ay_xp2, ay_three);
    let le_4_xp1 = terms.mk_le(ay_four, ay_xp1);
    let not_le_xp2_3 = terms.mk_not(le_xp2_3);
    let not_le_4_xp1 = terms.mk_not(le_4_xp1);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_xp2_3, not_le_4_xp1],
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}
