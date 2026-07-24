// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symbolic Real contradiction-closeout regressions.

use super::*;
use crate::tactic::arith_linarith_proof::build_add_le_add_proof;
use crate::tactic::tc_app;

fn init_symbolic_real_env(int_context: &str, real_context: &str) -> Environment {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas().expect(int_context);
    env.init_real_linear_order().expect(real_context);
    env
}

fn init_symbolic_real_hadd_env() -> Environment {
    let mut env = init_symbolic_real_env(
        "Int ordering lemmas should initialize for symbolic Real HAdd closeout",
        "Real linear order axioms should initialize for symbolic Real HAdd closeout",
    );
    env.init_real_hadd_inst()
        .expect("Real HAdd instance should initialize for symbolic Real HAdd closeout");
    env
}

fn make_real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

fn make_real_hadd(lhs: Expr, rhs: Expr) -> Expr {
    let real = Expr::const_(Name::from_string("Real"), vec![]);
    tc_app::mk_tc_hbinop(
        Expr::const_(
            Name::from_string("HAdd.hAdd"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        real.clone(),
        real.clone(),
        real,
        Expr::const_(Name::from_string("instHAddReal"), vec![]),
        lhs,
        rhs,
    )
}

fn symbolic_int_false_state(env: Environment, h_ty: Expr) -> (ProofState, FVarId, FVarId) {
    let m_id = FVarId::new(0);
    let h_id = FVarId::new(1);
    let state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                fvar: m_id,
                name: "m".into(),
                ty: Expr::const_(Name::from_string("Int"), vec![]),
                value: None,
            },
            LocalDecl {
                fvar: h_id,
                name: "h".into(),
                ty: h_ty,
                value: None,
            },
        ],
    );
    (state, m_id, h_id)
}

fn assert_goal_closes(state: &mut ProofState, goal: &Goal, proof: Expr, context: &str) {
    let result = state.close_goal(goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept the {context} proof, got: {result:?}"
    );
    assert!(state.is_complete(), "{context} proof should close the goal");
}

/// Symbolic integer-valued Real contradiction via additive tree downcast (#2621).
///
/// Hypothesis shape:
///   h : Real.add(Real.ofInt m)(Real.ofNat 5) ≤ Real.add(Real.ofInt m)(Real.ofNat 3)
///
/// After downcast, this becomes `Int.add m 5 ≤ Int.add m 3`, where `m` is symbolic.
/// The Int contradiction closer cancels the shared left addend via
/// `Int.le_of_add_le_add_left` to get `5 ≤ 3`, then closes concretely.
#[test]
fn test_linarith_real_symbolic_int_additive_contradiction_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = init_symbolic_real_env(
        "Int ordering lemmas should initialize for symbolic Real additive closeout",
        "Real linear order axioms should initialize for symbolic Real additive closeout",
    );
    let m_id = FVarId::new(0);
    let m = Expr::fvar(m_id);
    let h_ty = make_real_le_tc(
        make_real_add(make_real_ofint(m.clone()), make_real_ofnat(5)),
        make_real_add(make_real_ofint(m.clone()), make_real_ofnat(3)),
    );

    let (mut state, _, h_id) = symbolic_int_false_state(env, h_ty);
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("symbolic integer-valued Real additive contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "False.elim"),
        "symbolic Real additive contradiction must close with False.elim"
    );
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "symbolic Real additive contradiction must downcast to Int via Real.ofInt_le_to_Int"
    );
    assert!(
        expr_contains_const(&proof, "Int.le_of_add_le_add_left")
            || expr_contains_const(&proof, "Int.le_of_add_le_add_right"),
        "symbolic Real additive contradiction must cancel the shared addend"
    );

    assert_goal_closes(
        &mut state,
        &goal,
        proof,
        "symbolic Real additive contradiction",
    );
}

/// Single symbolic integer-valued Real contradiction using `HAdd.hAdd` syntax.
///
/// This exercises the direct single-hypothesis closeout path, where the
/// contradiction closer sees the original endpoint expressions rather than the
/// canonical `Real.add` terms built by the accumulation helpers.
#[test]
fn test_linarith_real_symbolic_int_hadd_contradiction_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = init_symbolic_real_hadd_env();
    let m_id = FVarId::new(0);
    let m = Expr::fvar(m_id);
    let h_ty = make_real_le_tc(
        make_real_hadd(make_real_ofint(m.clone()), make_real_ofnat(5)),
        make_real_hadd(make_real_ofint(m.clone()), make_real_ofnat(3)),
    );

    let (mut state, _, h_id) = symbolic_int_false_state(env, h_ty);
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("symbolic HAdd-based Real contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "False.elim"),
        "symbolic HAdd-based Real contradiction must close with False.elim"
    );
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "symbolic HAdd-based Real contradiction must downcast via Real.ofInt_le_to_Int"
    );
    assert!(
        expr_contains_const(&proof, "Int.le_of_add_le_add_left")
            || expr_contains_const(&proof, "Int.le_of_add_le_add_right"),
        "symbolic HAdd-based Real contradiction must cancel the shared addend"
    );

    assert_goal_closes(
        &mut state,
        &goal,
        proof,
        "symbolic HAdd-based Real contradiction",
    );
}

/// Symbolic integer-valued Real contradiction with shared right addend (#2621).
///
/// Hypothesis shape:
///   h : Real.add(Real.ofNat 5)(Real.ofInt m) ≤ Real.add(Real.ofNat 3)(Real.ofInt m)
///
/// After downcast, `Int.add 5 m ≤ Int.add 3 m`. The shared right addend `m`
/// is canceled via `Int.le_of_add_le_add_right`.
#[test]
fn test_linarith_real_symbolic_int_additive_right_cancel_closes_goal() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = init_symbolic_real_env(
        "Int ordering lemmas should initialize for symbolic right-cancel test",
        "Real linear order axioms should initialize for symbolic right-cancel test",
    );
    let m_id = FVarId::new(0);
    let m = Expr::fvar(m_id);
    let h_ty = make_real_le_tc(
        make_real_add(make_real_ofnat(5), make_real_ofint(m.clone())),
        make_real_add(make_real_ofnat(3), make_real_ofint(m.clone())),
    );

    let (mut state, _, h_id) = symbolic_int_false_state(env, h_ty);
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1],
        result_constant: 2,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("symbolic right-cancel Real additive contradiction should produce a proof");
    assert!(
        expr_contains_const(&proof, "False.elim"),
        "symbolic right-cancel must close with False.elim"
    );
    assert!(
        expr_contains_const(&proof, "Int.le_of_add_le_add_right"),
        "symbolic right-cancel must use Int.le_of_add_le_add_right"
    );

    assert_goal_closes(&mut state, &goal, proof, "symbolic right-cancel");
}

#[test]
fn test_linarith_real_additive_mixed_symbolic_keeps_real_path() {
    let mut env = Environment::with_prelude();
    env.init_real_linear_order()
        .expect("Real linear order axioms should initialize for mixed Real accumulation test");

    let x_id = FVarId::new(0);
    let y_id = FVarId::new(1);
    let h1_id = FVarId::new(2);
    let h2_id = FVarId::new(3);
    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);
    let concrete_lhs = make_real_ofnat(5);
    let concrete_rhs = make_real_ofnat(3);
    let goal_target = make_real_le_tc(
        make_real_add(x.clone(), concrete_lhs.clone()),
        make_real_add(y.clone(), concrete_rhs.clone()),
    );

    let mut state = ProofState::with_context(
        env,
        goal_target,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: Expr::const_(Name::from_string("Real"), vec![]),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: Expr::const_(Name::from_string("Real"), vec![]),
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: make_real_le_tc(x, y),
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: make_real_le_tc(concrete_lhs, concrete_rhs),
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = build_add_le_add_proof(&[(0, 1), (1, 1)], &[h1_id, h2_id], &goal)
        .expect("mixed symbolic+concrete Real bounds should still combine in Real");
    assert!(
        expr_contains_const(&proof, "Real.le_trans"),
        "mixed Real accumulation should stay on the Real add/transitivity path"
    );
    assert!(
        !expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "mixed Real accumulation must not partially downcast only the concrete hypothesis"
    );

    assert_goal_closes(&mut state, &goal, proof, "mixed Real additive");
}
