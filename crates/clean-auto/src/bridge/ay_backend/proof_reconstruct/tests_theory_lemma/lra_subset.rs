// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for disconnected subset replay in LRA Farkas reconstruction.

use super::support::boundary::assert_lra_trust_boundary;
use super::support::semantic::{
    mk_real_int_const, register_int_const, register_int_var, register_real_var,
};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, Sort, TermStore, VariableMapping,
};

fn mk_real_ofint_expr(int_expr: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr.clone(),
    )
}

fn build_int_symbolic_subset_result() -> super::super::ReconstructionResult {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_41", 41);
    let y = register_int_var(&mut terms, &mut map, "fvar_42", 42);
    let u = register_int_var(&mut terms, &mut map, "fvar_43", 43);
    let v = register_int_var(&mut terms, &mut map, "fvar_44", 44);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);

    let x_plus_3 = terms.mk_add(vec![x, three]);
    let y_plus_2 = terms.mk_add(vec![y, two]);
    let le_x3_y = terms.mk_le(x_plus_3, y);
    let le_y2_x = terms.mk_le(y_plus_2, x);
    let le_uv = terms.mk_le(u, v);
    let not_le_x3_y = terms.mk_not(le_x3_y);
    let not_le_y2_x = terms.mk_not(le_y2_x);
    let not_le_uv = terms.mk_not(le_uv);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_x3_y, not_le_y2_x, not_le_uv],
        FarkasAnnotation::from_ints(&[1, 1, 1]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    attempt_reconstruction(&proof, &terms, &map, &negated_goal)
}

fn build_real_symbolic_subset_result() -> super::super::ReconstructionResult {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let test_x = mk_real_ofint_expr(&Expr::const_(Name::from_string("testXI"), vec![]));
    let test_y = mk_real_ofint_expr(&Expr::const_(Name::from_string("testYI"), vec![]));
    let x = terms.mk_var("testX", Sort::Real);
    let y = terms.mk_var("testY", Sort::Real);
    let u = register_real_var(&mut terms, &mut map, "fvar_43", 43);
    let v = register_real_var(&mut terms, &mut map, "fvar_44", 44);
    let three = mk_real_int_const(&mut terms, 3);
    let two = mk_real_int_const(&mut terms, 2);
    map.register_var("testX", test_x, real_ty.clone());
    map.register_var("testY", test_y, real_ty);

    let x_plus_3 = terms.mk_add(vec![x, three]);
    let y_plus_2 = terms.mk_add(vec![y, two]);
    let le_x3_y = terms.mk_le(x_plus_3, y);
    let le_y2_x = terms.mk_le(y_plus_2, x);
    let le_uv = terms.mk_le(u, v);
    let not_le_x3_y = terms.mk_not(le_x3_y);
    let not_le_y2_x = terms.mk_not(le_y2_x);
    let not_le_uv = terms.mk_not(le_uv);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_x3_y, not_le_y2_x, not_le_uv],
        FarkasAnnotation::from_ints(&[1, 1, 1]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    attempt_reconstruction(&proof, &terms, &map, &negated_goal)
}

#[test]
fn test_theory_lemma_lra_farkas_symbolic_additive_subset_ignores_unrelated_active_bound() {
    let result = build_int_symbolic_subset_result();

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lra_farkas_real_symbolic_additive_subset_ignores_unrelated_active_bound() {
    let result = build_real_symbolic_subset_result();

    assert_lra_trust_boundary(&result, 0);
}
