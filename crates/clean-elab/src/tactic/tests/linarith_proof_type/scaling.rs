// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scaling-boundary regressions for linarith proof reconstruction.

use super::*;
use crate::tactic::arith_linarith_proof::build_scaled_proof;

fn make_real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_build_scaled_proof_real_single_typechecks() {
    let mut env = Environment::with_prelude();
    env.init_real_linear_order()
        .expect("Real linear order axioms should initialize for scaled proof test");

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let x_id = FVarId::new(0);
    let y_id = FVarId::new(1);
    let h_id = FVarId::new(2);
    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);
    let triple_x = make_real_add(make_real_add(x.clone(), x.clone()), x.clone());
    let triple_y = make_real_add(make_real_add(y.clone(), y.clone()), y.clone());

    let mut state = ProofState::with_context(
        env,
        make_real_le_tc(triple_x, triple_y),
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: real_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: real_ty,
                value: None,
            },
            LocalDecl {
                fvar: h_id,
                name: "h".into(),
                ty: make_real_le_tc(x, y),
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = build_scaled_proof(&[(0, 3)], &[h_id], &goal)
        .expect("Real scaled proof should be reconstructed via repeated addition");
    assert!(
        expr_contains_const(&proof, "Real.le_trans"),
        "Real coeff=3 scaling must use repeated-add reconstruction"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept the Real scaled proof term, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed by the Real scaled proof"
    );
}

/// Compact Int scaling: coefficient i64::MAX + 1 now succeeds via
/// `Int.mul_le_mul_of_nonneg_left` instead of the old repeated-add path (#2630).
///
/// Part of #2630.
#[test]
fn test_build_scaled_proof_int_coeff_above_i64_uses_compact_mul() {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int order lemmas required for compact scaling");
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let x_id = FVarId::new(0);
    let y_id = FVarId::new(1);
    let h_id = FVarId::new(2);
    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    let state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: int_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: int_ty,
                value: None,
            },
            LocalDecl {
                fvar: h_id,
                name: "h".into(),
                ty: make_int_le_tc(x, y),
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();

    let coeff = i128::from(i64::MAX) + 1;
    let proof = build_scaled_proof(&[(0, coeff)], &[h_id], &goal);
    assert!(
        proof.is_some(),
        "Int coeff i64::MAX+1 must succeed via compact mul scaling"
    );
    let proof = proof.unwrap();
    assert!(
        expr_contains_const(&proof, "Int.mul_le_mul_of_nonneg_left"),
        "compact scaling must use Int.mul_le_mul_of_nonneg_left, not repeated add"
    );
}

/// Fail-closed: coefficients above u64::MAX still return None (#2630).
///
/// Part of #2630.
#[test]
fn test_build_scaled_proof_int_coeff_above_u64_returns_none() {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int order lemmas required");
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let x_id = FVarId::new(0);
    let y_id = FVarId::new(1);
    let h_id = FVarId::new(2);
    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    let state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: int_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: int_ty,
                value: None,
            },
            LocalDecl {
                fvar: h_id,
                name: "h".into(),
                ty: make_int_le_tc(x, y),
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();

    let coeff = i128::from(u64::MAX) + 1;
    let proof = build_scaled_proof(&[(0, coeff)], &[h_id], &goal);
    assert!(
        proof.is_none(),
        "Int coeff above u64::MAX must fail closed at numeral ceiling"
    );
}
