// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Chain-closeout regressions for sort-generic linarith replay.

use super::*;

fn make_nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::nat_lt_tc(lhs, rhs)
}

fn make_int_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LT.lt", "Int", "instLTInt", lhs, rhs)
}

fn make_real_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LT.lt", "Real", "instLTReal", lhs, rhs)
}

fn three_hyp_nat_chain_state(env: Environment) -> (ProofState, [FVarId; 3]) {
    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);
    let h3_id = FVarId::new(2);
    let state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3)),
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1)),
                value: None,
            },
            LocalDecl {
                fvar: h3_id,
                name: "h3".into(),
                ty: make_nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(0)),
                value: None,
            },
        ],
    );
    (state, [h1_id, h2_id, h3_id])
}

/// Phase E.3: 3-hypothesis Nat le_trans chain produces a valid proof.
///
/// Given h1: 5 ≤ 3, h2: 3 ≤ 1, h3: 1 ≤ 0 → proves 5 ≤ 0 → derives False.
/// Before Phase E.3, build_linarith_proof returned None for 3+ hypotheses.
///
/// Part of #2422.
#[test]
fn test_linarith_three_hyp_chain_produces_proof() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let (state, [h1_id, h2_id, h3_id]) = three_hyp_nat_chain_state(Environment::with_prelude());
    let goal = state.current_goal().expect("should have a goal");
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1, 1],
        result_constant: 5,
    };
    let proof = build_linarith_proof(&state, goal, &certificate, &[h1_id, h2_id, h3_id]);
    assert!(
        proof.is_some(),
        "build_linarith_proof must handle 3-hypothesis Nat chain (Phase E.3)"
    );
}

/// Phase E.3: 3-hypothesis chain closes goal via close_goal.
///
/// Part of #2422.
#[test]
fn test_linarith_three_hyp_chain_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let (mut state, [h1_id, h2_id, h3_id]) = three_hyp_nat_chain_state(Environment::with_prelude());
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1, 1],
        result_constant: 5,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id, h3_id])
        .expect("should produce proof for 3-hyp chain");

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept 3-hyp chain proof, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");
}

/// Non-chaining hypotheses combine via add_le_add to derive False.
///
/// h1: 3 ≤ 2, h2: 5 ≤ 4 don't chain (2 ≠ 5), but add_le_add produces
/// (3+5) ≤ (2+4) → 8 ≤ 6 which is a concrete Nat contradiction.
/// The SortLeAcc accumulator derives False from this (#2493).
///
/// Part of #2422, Part of #2493.
#[test]
fn test_linarith_non_chaining_hyps_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);
    let h1_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(4));

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id])
        .expect("non-chaining concrete Nat hypotheses should produce a False proof via add_le_add");

    assert!(
        expr_contains_const(&proof, "False.elim"),
        "non-chaining add_le_add proof must derive False from 8 ≤ 6 contradiction"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept the add_le_add contradiction proof, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");
}

fn assert_cyclic_chain_closes_with_lt_irrefl(
    env: Environment,
    sort_ty: Expr,
    h1_ty: Expr,
    h2_ty: Expr,
    irrefl_name: &str,
) {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let x_id = FVarId::new(0);
    let y_id = FVarId::new(1);
    let h1_id = FVarId::new(2);
    let h2_id = FVarId::new(3);

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: sort_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: sort_ty,
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1],
        result_constant: 0,
    };

    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id])
        .expect("cyclic strict chain should reconstruct a False proof");
    assert!(
        expr_contains_const(&proof, irrefl_name),
        "cyclic strict chain must close with {irrefl_name}"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "cyclic strict-chain proof should type-check for {irrefl_name}, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed by the cyclic chain proof"
    );
}

#[test]
fn test_linarith_nat_cyclic_strict_chain_closes_with_lt_irrefl() {
    let mut env = Environment::with_prelude();
    env.init_smt_bridge_nat_order_lemmas()
        .expect("Nat bridge order lemmas should initialize for cyclic chain test");
    let x = Expr::fvar(FVarId::new(0));
    let y = Expr::fvar(FVarId::new(1));

    assert_cyclic_chain_closes_with_lt_irrefl(
        env,
        Expr::const_(Name::from_string("Nat"), vec![]),
        make_nat_lt_tc(x.clone(), y.clone()),
        make_nat_le_tc(y, x),
        "Nat.lt_irrefl",
    );
}

#[test]
fn test_linarith_int_cyclic_strict_chain_closes_with_lt_irrefl() {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize for cyclic chain test");
    let x = Expr::fvar(FVarId::new(0));
    let y = Expr::fvar(FVarId::new(1));

    assert_cyclic_chain_closes_with_lt_irrefl(
        env,
        Expr::const_(Name::from_string("Int"), vec![]),
        make_int_lt_tc(x.clone(), y.clone()),
        make_int_le_tc(y, x),
        "Int.lt_irrefl",
    );
}

#[test]
fn test_linarith_real_cyclic_strict_chain_closes_with_lt_irrefl() {
    let mut env = Environment::with_prelude();
    env.init_real_linear_order()
        .expect("Real linear order axioms should initialize for cyclic chain test");
    let x = Expr::fvar(FVarId::new(0));
    let y = Expr::fvar(FVarId::new(1));

    assert_cyclic_chain_closes_with_lt_irrefl(
        env,
        Expr::const_(Name::from_string("Real"), vec![]),
        make_real_lt_tc(x.clone(), y.clone()),
        make_real_le_tc(y, x),
        "Real.lt_irrefl",
    );
}
