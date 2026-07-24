// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end weighted LRA Farkas proof reconstruction tests with kernel
//! TypeChecker validation.
//!
//! Keeps the weighted replay coverage out of the unweighted `tests_e2e_lra`
//! module so the Int-focused split stays small.
//! Part of #302.

use super::tests_e2e_lra::{mk_int_add_expr, mk_int_ofnat, mk_le_int, mk_le_real, mk_real_ofnat};
use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{FarkasAnnotation, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};
use num_rational::Rational64;

fn negated_false_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

fn mk_real_add_expr(a: &Expr, b: &Expr) -> Expr {
    super::expr_builders::mk_add(&Sort::Real, a, b)
}

fn mk_real_ofint_expr(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        a.clone(),
    )
}

fn mk_weighted_lra_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let four_int = mk_int_ofnat(4);
    let three_int = mk_int_ofnat(3);
    let zero_int = mk_int_ofnat(0);
    let hundred_int = mk_int_ofnat(100);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_zero = terms.mk_var("const0", Sort::Int);
    let ay_hundred = terms.mk_var("const100", Sort::Int);

    map.register_var("const4", four_int.clone(), int_ty.clone());
    map.register_var("const3", three_int.clone(), int_ty.clone());
    map.register_var("const0", zero_int.clone(), int_ty.clone());
    map.register_var("const100", hundred_int.clone(), int_ty.clone());

    let le_4_3 = terms.mk_le(ay_four, ay_three);
    let le_0_100 = terms.mk_le(ay_zero, ay_hundred);
    let not_le_4_3 = terms.mk_not(le_4_3);
    let not_le_0_100 = terms.mk_not(le_0_100);

    let le_4_3_prop = mk_le_int(&four_int, &three_int);
    let le_0_100_prop = mk_le_int(&zero_int, &hundred_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_4_le_3", h1_id, Expr::fvar(h1_id), le_4_3_prop.clone());
    map.register_hypothesis(
        "h_0_le_100",
        h2_id,
        Expr::fvar(h2_id),
        le_0_100_prop.clone(),
    );

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[200, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_3, not_le_0_100], farkas);
    let s1 = proof.add_assume(le_4_3, None);
    let s2 = proof.add_resolution(vec![not_le_0_100], not_le_4_3, s0, s1);
    let s3 = proof.add_assume(le_0_100, None);
    proof.add_resolution(vec![], not_le_0_100, s2, s3);

    let hyps = vec![
        (h1_id, "h_4_le_3", le_4_3_prop),
        (h2_id, "h_0_le_100", le_0_100_prop),
    ];
    (terms, map, proof, hyps)
}

fn mk_weighted_real_lra_fractional_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let four_real = mk_real_ofnat(4);
    let three_real = mk_real_ofnat(3);
    let zero_real = mk_real_ofnat(0);
    let two_real = mk_real_ofnat(2);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_four = terms.mk_var("const4", Sort::Real);
    let ay_three = terms.mk_var("const3", Sort::Real);
    let ay_zero = terms.mk_var("const0", Sort::Real);
    let ay_two = terms.mk_var("const2", Sort::Real);

    map.register_var("const4", four_real.clone(), real_ty.clone());
    map.register_var("const3", three_real.clone(), real_ty.clone());
    map.register_var("const0", zero_real.clone(), real_ty.clone());
    map.register_var("const2", two_real.clone(), real_ty.clone());

    let le_4_3 = terms.mk_le(ay_four, ay_three);
    let le_0_2 = terms.mk_le(ay_zero, ay_two);
    let not_le_4_3 = terms.mk_not(le_4_3);
    let not_le_0_2 = terms.mk_not(le_0_2);

    let le_4_3_prop = mk_le_real(&four_real, &three_real);
    let le_0_2_prop = mk_le_real(&zero_real, &two_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_4_le_3", h1_id, Expr::fvar(h1_id), le_4_3_prop.clone());
    map.register_hypothesis("h_0_le_2", h2_id, Expr::fvar(h2_id), le_0_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::new(vec![Rational64::new(3, 2), Rational64::new(1, 2)]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_4_3, not_le_0_2], farkas);
    let s1 = proof.add_assume(le_4_3, None);
    let s2 = proof.add_resolution(vec![not_le_0_2], not_le_4_3, s0, s1);
    let s3 = proof.add_assume(le_0_2, None);
    proof.add_resolution(vec![], not_le_0_2, s2, s3);

    let hyps = vec![
        (h1_id, "h_4_le_3", le_4_3_prop),
        (h2_id, "h_0_le_2", le_0_2_prop),
    ];
    (terms, map, proof, hyps)
}

fn mk_weighted_symbolic_lra_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
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
    let le_x_1_a = terms.mk_le(ay_x, ay_one);
    let le_x_1_b = terms.mk_le(ay_x, ay_one);
    let le_y_2_a = terms.mk_le(ay_y, ay_two);
    let le_y_2_b = terms.mk_le(ay_y, ay_two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1_a = terms.mk_not(le_x_1_a);
    let not_le_x_1_b = terms.mk_not(le_x_1_b);
    let not_le_y_2_a = terms.mk_not(le_y_2_a);
    let not_le_y_2_b = terms.mk_not(le_y_2_b);

    let le_4_xy_prop = mk_le_int(&four_int, &mk_int_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_int(&test_x, &one_int);
    let le_y_2_prop = mk_le_int(&test_y, &two_int);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    let h4_id = FVarId::new(13);
    let h5_id = FVarId::new(14);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1_a", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_x_le_1_b", h3_id, Expr::fvar(h3_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2_a", h4_id, Expr::fvar(h4_id), le_y_2_prop.clone());
    map.register_hypothesis("h_y_le_2_b", h5_id, Expr::fvar(h5_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1, 1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas(
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
    let s1 = proof.add_assume(le_4_xy, None);
    let s2 = proof.add_resolution(
        vec![not_le_x_1_a, not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_4_xy,
        s0,
        s1,
    );
    let s3 = proof.add_assume(le_x_1_a, None);
    let s4 = proof.add_resolution(
        vec![not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_x_1_a,
        s2,
        s3,
    );
    let s5 = proof.add_assume(le_x_1_b, None);
    let s6 = proof.add_resolution(vec![not_le_y_2_a, not_le_y_2_b], not_le_x_1_b, s4, s5);
    let s7 = proof.add_assume(le_y_2_a, None);
    let s8 = proof.add_resolution(vec![not_le_y_2_b], not_le_y_2_a, s6, s7);
    let s9 = proof.add_assume(le_y_2_b, None);
    proof.add_resolution(vec![], not_le_y_2_b, s8, s9);

    let hyps = vec![
        (h1_id, "h_4_le_xy", le_4_xy_prop),
        (h2_id, "h_x_le_1_a", le_x_1_prop.clone()),
        (h3_id, "h_x_le_1_b", le_x_1_prop),
        (h4_id, "h_y_le_2_a", le_y_2_prop.clone()),
        (h5_id, "h_y_le_2_b", le_y_2_prop),
    ];
    (terms, map, proof, hyps)
}

fn mk_weighted_symbolic_real_lra_ay_proof(
    constructor_form_consts: bool,
) -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let mk_real_const = |n| {
        if !constructor_form_consts {
            return mk_real_ofnat(n);
        }
        let mut nat = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        for _ in 0..n {
            nat = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat);
        }
        Expr::app(Expr::const_(Name::from_string("Real.ofNat"), vec![]), nat)
    };
    let four_real = mk_real_const(4);
    let one_real = mk_real_const(1);
    let two_real = mk_real_const(2);
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
    let le_x_1_a = terms.mk_le(ay_x, ay_one);
    let le_x_1_b = terms.mk_le(ay_x, ay_one);
    let le_y_2_a = terms.mk_le(ay_y, ay_two);
    let le_y_2_b = terms.mk_le(ay_y, ay_two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1_a = terms.mk_not(le_x_1_a);
    let not_le_x_1_b = terms.mk_not(le_x_1_b);
    let not_le_y_2_a = terms.mk_not(le_y_2_a);
    let not_le_y_2_b = terms.mk_not(le_y_2_b);

    let le_4_xy_prop = mk_le_real(&four_real, &mk_real_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_real(&test_x, &one_real);
    let le_y_2_prop = mk_le_real(&test_y, &two_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    let h4_id = FVarId::new(13);
    let h5_id = FVarId::new(14);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1_a", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_x_le_1_b", h3_id, Expr::fvar(h3_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2_a", h4_id, Expr::fvar(h4_id), le_y_2_prop.clone());
    map.register_hypothesis("h_y_le_2_b", h5_id, Expr::fvar(h5_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1, 1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas(
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
    let s1 = proof.add_assume(le_4_xy, None);
    let s2 = proof.add_resolution(
        vec![not_le_x_1_a, not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_4_xy,
        s0,
        s1,
    );
    let s3 = proof.add_assume(le_x_1_a, None);
    let s4 = proof.add_resolution(
        vec![not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_x_1_a,
        s2,
        s3,
    );
    let s5 = proof.add_assume(le_x_1_b, None);
    let s6 = proof.add_resolution(vec![not_le_y_2_a, not_le_y_2_b], not_le_x_1_b, s4, s5);
    let s7 = proof.add_assume(le_y_2_a, None);
    let s8 = proof.add_resolution(vec![not_le_y_2_b], not_le_y_2_a, s6, s7);
    let s9 = proof.add_assume(le_y_2_b, None);
    proof.add_resolution(vec![], not_le_y_2_b, s8, s9);

    let hyps = vec![
        (h1_id, "h_4_le_xy", le_4_xy_prop),
        (h2_id, "h_x_le_1_a", le_x_1_prop.clone()),
        (h3_id, "h_x_le_1_b", le_x_1_prop),
        (h4_id, "h_y_le_2_a", le_y_2_prop.clone()),
        (h5_id, "h_y_le_2_b", le_y_2_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_weighted_lra_additive_type_checks() {
    let (terms, map, proof, _hyps) = mk_weighted_lra_ay_proof();
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

#[test]
fn test_e2e_weighted_real_lra_fractional_lcm_type_checks() {
    let (terms, map, proof, _hyps) = mk_weighted_real_lra_fractional_ay_proof();
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

#[test]
fn test_e2e_weighted_symbolic_lra_additive_type_checks() {
    let (terms, map, proof, _hyps) = mk_weighted_symbolic_lra_ay_proof();
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

#[test]
fn test_e2e_weighted_symbolic_real_lra_additive_reconstructs_zero_trust() {
    let (terms, map, proof, _hyps) = mk_weighted_symbolic_real_lra_ay_proof(true);
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
