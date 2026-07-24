// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2e tests for cyclic and transitivity chain closers.
//!
//! - Real cyclic strict chains (`lt_irrefl`)
//! - `LiaGeneric` delegation through the Int concrete closer

use super::support::*;
use super::*;

fn mk_real_lra_cyclic_case() -> ArithmeticE2eCase {
    let env = mk_env_for_real_arith();
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_x = terms.mk_var("testX", Sort::Real);
    let ay_y = terms.mk_var("testY", Sort::Real);
    map.register_var("testX", test_x.clone(), real_ty.clone());
    map.register_var("testY", test_y.clone(), real_ty);

    let lt_xy = terms.mk_lt(ay_x, ay_y);
    let le_yx = terms.mk_le(ay_y, ay_x);
    let not_lt_xy = terms.mk_not(lt_xy);
    let not_le_yx = terms.mk_not(le_yx);

    let lt_xy_prop = mk_lt_real(&test_x, &test_y);
    let le_yx_prop = mk_le_real(&test_y, &test_x);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_lt_xy", h1_id, Expr::fvar(h1_id), lt_xy_prop.clone());
    map.register_hypothesis("h_le_yx", h2_id, Expr::fvar(h2_id), le_yx_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_xy, not_le_yx], farkas);
    let s1 = proof.add_assume(lt_xy, None);
    let s2 = proof.add_resolution(vec![not_le_yx], not_lt_xy, s0, s1);
    let s3 = proof.add_assume(le_yx, None);
    proof.add_resolution(vec![], not_le_yx, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_lt_xy", lt_xy_prop),
            (h2_id, "h_le_yx", le_yx_prop),
        ],
        context: "Real cyclic LRA e2e",
    }
}

fn mk_lia_generic_mixed_chain_case() -> ArithmeticE2eCase {
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

    let le_5x = terms.mk_le(ay_five, ay_x);
    let lt_xy = terms.mk_lt(ay_x, ay_y);
    let le_y3 = terms.mk_le(ay_y, ay_three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_lt_xy = terms.mk_not(lt_xy);
    let not_le_y3 = terms.mk_not(le_y3);

    let le_5x_prop = mk_le_int(&five, &test_x);
    let lt_xy_prop = mk_lt_int(&test_x, &test_y);
    let le_y3_prop = mk_le_int(&test_y, &three);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_5_le_x", h1_id, Expr::fvar(h1_id), le_5x_prop.clone());
    map.register_hypothesis("h_x_lt_y", h2_id, Expr::fvar(h2_id), lt_xy_prop.clone());
    map.register_hypothesis("h_y_le_3", h3_id, Expr::fvar(h3_id), le_y3_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_5x, not_lt_xy, not_le_y3],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(le_5x, None);
    let s2 = proof.add_resolution(vec![not_lt_xy, not_le_y3], not_le_5x, s0, s1);
    let s3 = proof.add_assume(lt_xy, None);
    let s4 = proof.add_resolution(vec![not_le_y3], not_lt_xy, s2, s3);
    let s5 = proof.add_assume(le_y3, None);
    proof.add_resolution(vec![], not_le_y3, s4, s5);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_x", le_5x_prop),
            (h2_id, "h_x_lt_y", lt_xy_prop),
            (h3_id, "h_y_le_3", le_y3_prop),
        ],
        context: "LiaGeneric mixed chain e2e",
    }
}

#[test]
fn test_e2e_real_lra_cyclic_lt_irrefl_type_checks() {
    assert_case_type_checks(mk_real_lra_cyclic_case());
}

#[test]
fn test_e2e_lia_generic_mixed_chain_type_checks() {
    let case = mk_lia_generic_mixed_chain_case();
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
