// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct Real distributivity bridge regressions for scaled replay (#2635).

use super::*;
use clean_kernel::{env::Declaration, ExprKind};
use pattern::linear_combination_proof::build_linear_combination_eq_proof;

fn real_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn real_of_int(n: i64) -> Expr {
    let int_expr = if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n.unsigned_abs() - 1),
        )
    };
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn real_mul_expr(coeff: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), coeff),
        rhs,
    )
}

fn real_mul(coeff: i64, rhs: Expr) -> Expr {
    real_mul_expr(real_of_int(coeff), rhs)
}

fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

fn setup_real_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_real_complex_analysis()
        .expect("Real complex analysis should initialize");
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");
    env
}

fn setup_real_scaled_replay_goal(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(real.clone(), goal_lhs, goal_rhs),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(
                    real.clone(),
                    real_mul(2, real_var("a")),
                    real_mul(2, real_var("b")),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(real, real_var("c"), real_var("d")),
                value: None,
            },
        ],
    )
}

fn assert_clean_real_proof(state: &ProofState, context: &str) {
    assert!(state.is_complete(), "{context}: state should be complete");
    assert!(
        state.proof_term().is_some(),
        "{context}: proof_term() should be extractable"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context}: trustedArith should stay at 0"
    );
    assert_eq!(ledger.sorry_count, 0, "{context}: sorry should stay at 0");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "{context}: trustedAy should stay at 0"
    );
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name == &Name::from_string(needle),
        ExprKind::App(f, a) => expr_contains_const(f, needle) || expr_contains_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, needle)
        }
        _ => false,
    }
}

#[test]
fn test_proof_builder_real_left_commuted_distrib_bridge_closes_without_trust() {
    let mut state = setup_real_scaled_replay_goal(
        real_mul(2, real_add(real_var("c"), real_var("a"))),
        real_add(real_mul(2, real_var("b")), real_mul(2, real_var("d"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::one("h1"), LinearCoeff::int("h2", 2)],
    )
    .expect("left commuted Real distributivity bridge should reconstruct a proof");
    assert!(
        expr_contains_const(&proof, "Real.distrib"),
        "left commuted Real distributivity bridge should use Real.distrib"
    );
    assert!(
        expr_contains_const(&proof, "Real.add_comm"),
        "left commuted Real distributivity bridge should use Real.add_comm"
    );

    state
        .close_goal(&goal, proof)
        .expect("left commuted Real distributivity bridge should close the goal");
    assert_clean_real_proof(&state, "Real left commuted distributivity bridge");
}

#[test]
fn test_proof_builder_real_right_commuted_distrib_bridge_closes_without_trust() {
    let mut state = setup_real_scaled_replay_goal(
        real_add(real_mul(2, real_var("a")), real_mul(2, real_var("c"))),
        real_mul(2, real_add(real_var("d"), real_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::one("h1"), LinearCoeff::int("h2", 2)],
    )
    .expect("right commuted Real distributivity bridge should reconstruct a proof");
    assert!(
        expr_contains_const(&proof, "Eq.symm"),
        "right commuted Real distributivity bridge should use Eq.symm"
    );
    assert!(
        expr_contains_const(&proof, "Real.distrib"),
        "right commuted Real distributivity bridge should use Real.distrib"
    );
    assert!(
        expr_contains_const(&proof, "Real.add_comm"),
        "right commuted Real distributivity bridge should use Real.add_comm"
    );

    state
        .close_goal(&goal, proof)
        .expect("right commuted Real distributivity bridge should close the goal");
    assert_clean_real_proof(&state, "Real right commuted distributivity bridge");
}
