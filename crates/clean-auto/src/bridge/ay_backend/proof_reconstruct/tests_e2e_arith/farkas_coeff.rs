// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2e tests for Farkas coefficient pruning and symbolic-tail handling.
//!
//! - Zero-coefficient bounds pruned to single-bound closer
//! - Concrete single-bound contradiction with active symbolic tail

use super::support::*;
use super::*;

fn register_test_hypothesis(map: &mut VariableMapping, name: &str, id: FVarId, prop: &Expr) {
    map.register_hypothesis(name, id, Expr::fvar(id), prop.clone());
}

fn mk_three_literal_lra_resolution(
    not_le_3_2: ay_core::TermId,
    not_le_5_4: ay_core::TermId,
    not_le_xy: ay_core::TermId,
    le_3_2: ay_core::TermId,
    le_5_4: ay_core::TermId,
    le_xy: ay_core::TermId,
) -> Proof {
    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 =
        proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4, not_le_xy], farkas);
    let s1 = proof.add_assume(le_3_2, None);
    let s2 = proof.add_resolution(vec![not_le_5_4, not_le_xy], not_le_3_2, s0, s1);
    let s3 = proof.add_assume(le_5_4, None);
    let s4 = proof.add_resolution(vec![not_le_xy], not_le_5_4, s2, s3);
    let s5 = proof.add_assume(le_xy, None);
    proof.add_resolution(vec![], not_le_xy, s4, s5);
    proof
}

fn mk_lra_zero_coeff_pruned_single_bound_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five = mk_int_ofnat(5);
    let three = mk_int_ofnat(3);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const5", five.clone(), int_ty.clone());
    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty);

    let le_5_3 = terms.mk_le(ay_five, ay_three);
    let le_xy = terms.mk_le(ay_x, ay_y);
    let not_le_5_3 = terms.mk_not(le_5_3);
    let not_le_xy = terms.mk_not(le_xy);

    let le_5_3_prop = mk_le_int(&five, &three);
    let le_xy_prop = mk_le_int(&test_x, &test_y);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    register_test_hypothesis(&mut map, "h_5_le_3", h1_id, &le_5_3_prop);
    register_test_hypothesis(&mut map, "h_x_le_y", h2_id, &le_xy_prop);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 0]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_3, not_le_xy], farkas);
    let s1 = proof.add_assume(le_5_3, None);
    let s2 = proof.add_resolution(vec![not_le_xy], not_le_5_3, s0, s1);
    let s3 = proof.add_assume(le_xy, None);
    proof.add_resolution(vec![], not_le_xy, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_3", le_5_3_prop),
            (h2_id, "h_x_le_y", le_xy_prop),
        ],
        context: "zero-coefficient pruned single-bound e2e",
    }
}

fn mk_lra_concrete_single_bound_with_active_symbolic_tail_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five = mk_int_ofnat(5);
    let three = mk_int_ofnat(3);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const5", five.clone(), int_ty.clone());
    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty);

    let le_5_3 = terms.mk_le(ay_five, ay_three);
    let le_xy = terms.mk_le(ay_x, ay_y);
    let not_le_5_3 = terms.mk_not(le_5_3);
    let not_le_xy = terms.mk_not(le_xy);

    let le_5_3_prop = mk_le_int(&five, &three);
    let le_xy_prop = mk_le_int(&test_x, &test_y);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    register_test_hypothesis(&mut map, "h_5_le_3", h1_id, &le_5_3_prop);
    register_test_hypothesis(&mut map, "h_x_le_y", h2_id, &le_xy_prop);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5_3, not_le_xy], farkas);
    let s1 = proof.add_assume(le_5_3, None);
    let s2 = proof.add_resolution(vec![not_le_xy], not_le_5_3, s0, s1);
    let s3 = proof.add_assume(le_xy, None);
    proof.add_resolution(vec![], not_le_xy, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_3", le_5_3_prop),
            (h2_id, "h_x_le_y", le_xy_prop),
        ],
        context: "active symbolic tail with concrete single-bound contradiction e2e",
    }
}

fn mk_lra_concrete_subset_additive_with_active_symbolic_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let three = mk_int_ofnat(3);
    let two = mk_int_ofnat(2);
    let five = mk_int_ofnat(5);
    let four = mk_int_ofnat(4);
    let (test_x, test_y) = (
        Expr::const_(Name::from_string("testX"), vec![]),
        Expr::const_(Name::from_string("testY"), vec![]),
    );

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_x = terms.mk_var("testX", Sort::Int);
    let ay_y = terms.mk_var("testY", Sort::Int);

    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("const2", two.clone(), int_ty.clone());
    map.register_var("const5", five.clone(), int_ty.clone());
    map.register_var("const4", four.clone(), int_ty.clone());
    map.register_var("testX", test_x.clone(), int_ty.clone());
    map.register_var("testY", test_y.clone(), int_ty);

    let le_3_2 = terms.mk_le(ay_three, ay_two);
    let le_5_4 = terms.mk_le(ay_five, ay_four);
    let le_xy = terms.mk_le(ay_x, ay_y);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);
    let not_le_xy = terms.mk_not(le_xy);

    let (le_3_2_prop, le_5_4_prop, le_xy_prop) = (
        mk_le_int(&three, &two),
        mk_le_int(&five, &four),
        mk_le_int(&test_x, &test_y),
    );

    let (h1_id, h2_id, h3_id) = (FVarId::new(10), FVarId::new(11), FVarId::new(12));
    register_test_hypothesis(&mut map, "h_3_le_2", h1_id, &le_3_2_prop);
    register_test_hypothesis(&mut map, "h_5_le_4", h2_id, &le_5_4_prop);
    register_test_hypothesis(&mut map, "h_x_le_y", h3_id, &le_xy_prop);

    let proof =
        mk_three_literal_lra_resolution(not_le_3_2, not_le_5_4, not_le_xy, le_3_2, le_5_4, le_xy);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_3_le_2", le_3_2_prop),
            (h2_id, "h_5_le_4", le_5_4_prop),
            (h3_id, "h_x_le_y", le_xy_prop),
        ],
        context: "concrete-subset additive contradiction with active symbolic bound e2e",
    }
}

#[test]
fn test_e2e_lra_zero_coefficient_pruned_single_bound_type_checks() {
    let case = mk_lra_zero_coeff_pruned_single_bound_case();
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
fn test_e2e_lra_concrete_single_bound_with_active_symbolic_tail_type_checks() {
    let case = mk_lra_concrete_single_bound_with_active_symbolic_tail_case();
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
fn test_e2e_lra_concrete_subset_additive_with_active_symbolic_type_checks() {
    let case = mk_lra_concrete_subset_additive_with_active_symbolic_case();
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
