// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete Real contradiction-closeout regressions.

use super::*;

fn init_real_downcast_env(int_context: &str, real_context: &str) -> Environment {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas().expect(int_context);
    env.init_real_linear_order().expect(real_context);
    env
}

fn false_goal() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn single_hyp_false_state(env: Environment, h_ty: Expr) -> (ProofState, FVarId) {
    let h_id = FVarId::new(0);
    let state = ProofState::with_context(
        env,
        false_goal(),
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );
    (state, h_id)
}

fn two_hyp_false_state(env: Environment, h1_ty: Expr, h2_ty: Expr) -> (ProofState, [FVarId; 2]) {
    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);
    let state = ProofState::with_context(
        env,
        false_goal(),
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
    (state, [h1_id, h2_id])
}

fn assert_goal_closes(state: &mut ProofState, goal: &Goal, proof: Expr, context: &str) {
    let result = state.close_goal(goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept the {context} proof, got: {result:?}"
    );
    assert!(state.is_complete(), "{context} proof should close the goal");
}

#[test]
fn test_linarith_real_additive_downcast_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = init_real_downcast_env(
        "Int ordering lemmas should initialize for Real-to-Int downcast path",
        "Real linear order axioms should initialize for additive Real test",
    );
    let (mut state, [h1_id, h2_id]) = two_hyp_false_state(
        env,
        make_real_le_tc(make_real_ofnat(5), make_real_ofnat(3)),
        make_real_le_tc(make_real_ofnat(4), make_real_ofnat(1)),
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id])
        .expect("Real additive downcast should produce a proof for non-chaining concrete bounds");
    assert!(
        expr_contains_const(&proof, "False.elim"),
        "Real additive proof must close the goal with False.elim"
    );
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "Real additive proof must use Real.ofInt_le_to_Int to downcast to Int"
    );

    assert_goal_closes(&mut state, &goal, proof, "Real additive downcast");
}

#[test]
fn test_linarith_real_scaled_downcast_closes_goal() {
    use crate::tactic::arith_linarith_proof::build_scaled_proof;

    let env = init_real_downcast_env(
        "Int ordering lemmas should initialize for Real scaled downcast path",
        "Real linear order axioms should initialize for scaled Real test",
    );
    let (mut state, h_id) =
        single_hyp_false_state(env, make_real_le_tc(make_real_ofnat(5), make_real_ofnat(3)));
    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = build_scaled_proof(&[(0, 3)], &[h_id], &goal)
        .expect("scaled concrete Real contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "scaled Real contradiction must downcast to Int before closeout"
    );
    assert!(
        expr_contains_const(&proof, "Int.NonNeg.casesOn"),
        "scaled Real contradiction must reuse the Int contradiction closeout path"
    );

    assert_goal_closes(&mut state, &goal, proof, "scaled Real contradiction");
}

/// Single Real hypothesis contradiction: h : Real.ofNat(5) ≤ Real.ofNat(3).
/// The generic closer must downcast to Int via `Real.ofInt_le_to_Int` and close
/// using the Int `NonNeg.casesOn` path. This exercises the `ArithSort::Real` arm
/// in `try_close_contradictory_le_generic` directly (#302 Phase 2).
#[test]
fn test_linarith_real_single_hypothesis_contradiction_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = init_real_downcast_env(
        "Int ordering lemmas should initialize for Real single-hyp closeout",
        "Real linear order axioms should initialize for single Real contradiction test",
    );
    let (mut state, h_id) =
        single_hyp_false_state(env, make_real_le_tc(make_real_ofnat(5), make_real_ofnat(3)));
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("single Real.ofNat contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "False.elim"),
        "single Real contradiction must close the goal with False.elim"
    );
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "single Real contradiction must downcast via Real.ofInt_le_to_Int"
    );
    assert!(
        expr_contains_const(&proof, "Int.NonNeg.casesOn"),
        "single Real contradiction must use the Int NonNeg closeout path after downcast"
    );

    assert_goal_closes(&mut state, &goal, proof, "single Real contradiction");
}

/// Single Real.ofInt hypothesis contradiction: h : Real.ofInt(-1) ≤ Real.ofInt(-3).
/// Like the ofNat test but uses `Real.ofInt` directly (skipping the normalization step).
#[test]
fn test_linarith_real_single_ofint_contradiction_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    fn int_negsucc(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n),
        )
    }

    let env = init_real_downcast_env(
        "Int ordering lemmas should initialize for Real.ofInt single-hyp closeout",
        "Real linear order axioms should initialize for ofInt contradiction test",
    );
    let (mut state, h_id) = single_hyp_false_state(
        env,
        make_real_le_tc(
            make_real_ofint(int_negsucc(0)),
            make_real_ofint(int_negsucc(2)),
        ),
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("single Real.ofInt contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "Real.ofInt contradiction must downcast via Real.ofInt_le_to_Int"
    );
    assert!(
        !expr_contains_const(&proof, "Real.ofNat_eq_ofInt"),
        "Real.ofInt endpoints should NOT need ofNat normalization"
    );

    assert_goal_closes(&mut state, &goal, proof, "Real.ofInt contradiction");
}
