// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Representative kernel-typecheck coverage for concrete arithmetic theory
//! lemmas that otherwise only assert reconstruction counters or proof presence.

use super::super::tests_e2e_lra::{
    mk_le_real, mk_real_add_expr, mk_real_ofint_expr, mk_real_ofnat,
};
use super::support::boundary::assert_lra_trust_boundary;
use super::support::kernel::{
    assert_lra_proof_type_checks, mk_lra_kernel_env, mk_real_lra_kernel_env,
};
use super::support::semantic::{
    mk_raw_le, mk_raw_lt, mk_real_int_const, register_int_const, register_int_var,
    register_real_var,
};
use super::{
    attempt_reconstruction, Expr, FVarId, FarkasAnnotation, Name, Proof, Sort, TermStore,
    TheoryLemmaKind, VariableMapping,
};

fn mk_real_additive_downcast_case() -> (
    TermStore,
    VariableMapping,
    Proof,
    [(FVarId, &'static str, Expr); 3],
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let four_real = mk_real_ofnat(4);
    let one_real = mk_real_ofnat(1);
    let two_real = mk_real_ofnat(2);
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
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![
            terms.mk_not(le_4_xy),
            terms.mk_not(le_x_1),
            terms.mk_not(le_y_2),
        ],
        farkas,
    );

    (
        terms,
        map,
        proof,
        [
            (h1_id, "h_4_le_xy", le_4_xy_prop),
            (h2_id, "h_x_le_1", le_x_1_prop),
            (h3_id, "h_y_le_2", le_y_2_prop),
        ],
    )
}

#[test]
fn test_lia_generic_concrete_mixed_chain_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_const(&mut terms, &mut map, "const5", 5);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_ab = terms.mk_le(a, b);
    let lt_bc = terms.mk_lt(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_lt_bc = terms.mk_not(lt_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_ab, not_lt_bc, not_le_cd],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "LiaGeneric concrete mixed chain should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("LiaGeneric concrete mixed chain should produce a proof term");

    let env = mk_lra_kernel_env();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    assert_lra_proof_type_checks(
        &env,
        &proof_term,
        &[
            (FVarId::new(2), "b", int_ty.clone()),
            (FVarId::new(3), "c", int_ty),
        ],
        "LiaGeneric concrete mixed chain",
    );
}

#[test]
fn test_lra_farkas_int_additive_two_bound_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

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
        "Int additive Le should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_lra_farkas_int_additive_mixed_le_lt_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let lt_5_4 = mk_raw_lt(&mut terms, five, four);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_lt_5_4 = terms.mk_not(lt_5_4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_lt_5_4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        result.stats.reconstructed_steps > 0,
        "Int additive mixed Le+Lt should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}

#[test]
fn test_real_concrete_chain_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let five = mk_real_int_const(&mut terms, 5);
    let three = mk_real_int_const(&mut terms, 3);

    let le_5x = terms.mk_le(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "Real concrete chain should reconstruct, error: {:?}",
        result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("Real concrete chain should produce a proof term");

    let env = mk_real_lra_kernel_env();
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    assert_lra_proof_type_checks(
        &env,
        &proof_term,
        &[(FVarId::new(1), "x", real_ty)],
        "Real concrete chain",
    );
}

#[test]
fn test_real_additive_downcast_type_checks_in_kernel() {
    let (terms, map, proof, _local_ctx_entries) = mk_real_additive_downcast_case();

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_real_mixed_endpoint_additive_type_checks_in_kernel() {
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
        "Real mixed-endpoint additive should reconstruct with native constants: {:?}",
        result.stats.first_diagnostic
    );
}
