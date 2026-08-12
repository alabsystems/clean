// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for weighted additive Farkas replay (Part of #2581).

use super::super::expr_builders_arith::CmpOp;
use super::super::theory_lemma_lra::ActiveBound;
use super::super::theory_lemma_lra_chain::BoundInfo;
use super::super::theory_lemma_lra_weighted::build_weighted_additive_false;
use super::support::semantic::{mk_raw_le, register_int_const};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, VariableMapping,
};
use ay::Sort;
use ay_core::TermId;
use clean_kernel::ExprKind;

fn contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => contains_const(f, target) || contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const(ty, target) || contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const(ty, target)
                || contains_const(val, target)
                || contains_const(body, target)
        }
        _ => false,
    }
}

fn real_of_nat(value: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(value),
    )
}

fn real_of_neg_succ(value: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(value),
        ),
    )
}

fn mk_real_bound(op: CmpOp, lhs_expr: Expr, rhs_expr: Expr) -> BoundInfo {
    BoundInfo {
        sort: Sort::Real,
        op,
        lhs_term: TermId(0),
        rhs_term: TermId(1),
        lhs_expr,
        rhs_expr,
    }
}

#[test]
fn test_theory_lemma_lra_farkas_weighted_additive_contradicts_where_unweighted_does_not() {
    // Weighted regression: the unweighted sum is NOT contradictory, but the
    // certificate-weighted sum IS.
    //
    // Bounds:       4 ≤ 3,  0 ≤ 100
    // Coefficients: [200, 1]
    // Unweighted:   4+0=4 ≤ 103=3+100     → NOT violated
    // Weighted:     200*4+0=800 > 700=200*3+100  → violated!
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let zero = register_int_const(&mut terms, &mut map, "const0", 0);
    let hundred = register_int_const(&mut terms, &mut map, "const100", 100);

    let le_4_3 = mk_raw_le(&mut terms, four, three);
    let le_0_100 = mk_raw_le(&mut terms, zero, hundred);
    let not_le_4_3 = terms.mk_not(le_4_3);
    let not_le_0_100 = terms.mk_not(le_0_100);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[200, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_3, not_le_0_100], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    // The unweighted sum is not contradictory (4 ≤ 103), so the unweighted path
    // fails. The weighted path (200*4=800 > 700=200*3+100) should succeed.
    assert!(
        result.stats.reconstructed_steps > 0,
        "weighted additive should reconstruct where unweighted does not: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_fractional_coefficient_caught_by_unweighted() {
    // Fractional coefficient [1/2, 1]: the unweighted additive sum is already
    // contradictory, so the unweighted path catches it before LCM scaling.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);

    let le_4_3 = mk_raw_le(&mut terms, four, three);
    let le_5_2 = mk_raw_le(&mut terms, five, two);
    let not_le_4_3 = terms.mk_not(le_4_3);
    let not_le_5_2 = terms.mk_not(le_5_2);

    let mut proof = Proof::new();
    use num_rational::Rational64;
    let coeffs = vec![Rational64::new(1, 2), Rational64::from_integer(1)];
    let farkas = FarkasAnnotation::new(coeffs);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_3, not_le_5_2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "fractional coefficient caught by unweighted should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_fractional_coefficient_lcm_scaling() {
    // Fractional coefficient [3/2, 1/2]: the unweighted sum is NOT
    // contradictory, but LCM-scaling to [3, 1] produces a violated weighted
    // sum. This exercises the rationalize_to_positive_ints path (Part of #302).
    //
    // Bounds:       4 ≤ 3,  0 ≤ 2
    // Coefficients: [3/2, 1/2]
    // LCM of denoms: 2 → scaled: [3, 1]
    // Unweighted:   4+0=4 ≤ 5=3+2     → NOT violated
    // Weighted:     3*4+1*0=12 > 11=3*3+1*2  → violated!
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let zero = register_int_const(&mut terms, &mut map, "const0", 0);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);

    let le_4_3 = mk_raw_le(&mut terms, four, three);
    let le_0_2 = mk_raw_le(&mut terms, zero, two);
    let not_le_4_3 = terms.mk_not(le_4_3);
    let not_le_0_2 = terms.mk_not(le_0_2);

    let mut proof = Proof::new();
    use num_rational::Rational64;
    let coeffs = vec![Rational64::new(3, 2), Rational64::new(1, 2)];
    let farkas = FarkasAnnotation::new(coeffs);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_3, not_le_0_2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "fractional LCM scaling should reconstruct: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_theory_lemma_lra_farkas_weighted_symbolic_additive_uses_nf_closeout() {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let one = register_int_const(&mut terms, &mut map, "const1", 1);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty);

    let x_plus_y = terms.mk_add(vec![ay_x, ay_y]);
    let le_4_xy = mk_raw_le(&mut terms, four, x_plus_y);
    let le_x_1_a = terms.mk_le(ay_x, one);
    let le_x_1_b = terms.mk_le(ay_x, one);
    let le_y_2_a = terms.mk_le(ay_y, two);
    let le_y_2_b = terms.mk_le(ay_y, two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1_a = terms.mk_not(le_x_1_a);
    let not_le_x_1_b = terms.mk_not(le_x_1_b);
    let not_le_y_2_a = terms.mk_not(le_y_2_a);
    let not_le_y_2_b = terms.mk_not(le_y_2_b);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1, 1, 1, 1]);
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![
            not_le_4_xy,
            not_le_x_1_a,
            not_le_x_1_b,
            not_le_y_2_a,
            not_le_y_2_b,
        ],
        farkas,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    // Mixed symbolic+concrete: semantic validation passes (native constants
    // eliminate), but the symbolic variables prevent full contradiction.
    // The theory lemma step reconstructs but the proof doesn't derive ⊥.
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "symbolic NF closeout should reconstruct the theory lemma step"
    );
    assert!(
        !result.derives_empty_clause,
        "symbolic bounds prevent deriving empty clause"
    );
}

#[test]
fn test_build_weighted_additive_false_real_non_negative_downcasts_to_int() {
    let left = mk_real_bound(CmpOp::Le, real_of_nat(4), real_of_nat(3));
    let right = mk_real_bound(CmpOp::Le, real_of_nat(0), real_of_nat(100));
    let bounds = [
        ActiveBound {
            clause_idx: 0,
            bound: &left,
        },
        ActiveBound {
            clause_idx: 1,
            bound: &right,
        },
    ];

    let false_proof = build_weighted_additive_false(&Sort::Real, &bounds, &[200, 1], 2)
        .expect("weighted Real builder should downcast non-negative bounds to Int");

    assert!(
        contains_const(&false_proof, "Real.ofNat_eq_ofInt"),
        "Real.ofNat endpoints should normalize before weighted Int replay"
    );
    assert!(
        contains_const(&false_proof, "Real.ofInt_le_to_Int"),
        "weighted Real replay should convert <= bounds to Int before scaling"
    );
}

#[test]
fn test_build_weighted_additive_false_real_mixed_sign_uses_lt_downcast() {
    let left = mk_real_bound(CmpOp::Le, real_of_nat(3), real_of_neg_succ(0));
    let right = mk_real_bound(CmpOp::Lt, real_of_neg_succ(1), real_of_nat(0));
    let bounds = [
        ActiveBound {
            clause_idx: 0,
            bound: &left,
        },
        ActiveBound {
            clause_idx: 1,
            bound: &right,
        },
    ];

    let false_proof = build_weighted_additive_false(&Sort::Real, &bounds, &[2, 1], 2)
        .expect("weighted Real builder should downcast mixed-sign bounds to Int");

    assert!(
        contains_const(&false_proof, "Real.ofNat_eq_ofInt"),
        "mixed-sign weighted replay should normalize Real.ofNat endpoints"
    );
    assert!(
        contains_const(&false_proof, "Real.ofInt_lt_to_Int"),
        "weighted Real replay should convert < bounds to Int before scaling"
    );
}
