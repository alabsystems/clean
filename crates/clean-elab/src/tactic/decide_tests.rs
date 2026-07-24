// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for lightweight decide tactic.
//!
//! Part of #3082.

use super::tests::*;
use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;

// =========================================================================
// Helper builders
// =========================================================================

/// Build `@Eq.{1} Nat lhs rhs`
fn nat_eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs,
        ),
        rhs,
    )
}

// =========================================================================
// True / False goals
// =========================================================================

#[test]
fn test_decide_true() {
    // Goal: True
    let mut env = Environment::new();
    env.init_true_false().unwrap();

    let goal = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, goal);

    eval_decide(&mut state).expect("decide should close True");
    assert!(state.is_complete(), "proof state should be complete");
}

// =========================================================================
// Nat equality
// =========================================================================

#[test]
fn test_decide_nat_eq_reflexive() {
    // Goal: 5 = 5
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let five = Expr::nat_lit(5);
    let goal = nat_eq_goal(five.clone(), five);

    let mut state = ProofState::new(env, goal);
    eval_decide(&mut state).expect("decide should close 5 = 5");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_decide_nat_eq_computed() {
    // Goal: 2 + 3 = 5
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let add_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let goal = nat_eq_goal(add_expr, Expr::nat_lit(5));

    let mut state = ProofState::new(env, goal);
    eval_decide(&mut state).expect("decide should close 2 + 3 = 5");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_decide_nat_eq_false() {
    // Goal: 2 = 3 (should fail)
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let goal = nat_eq_goal(Expr::nat_lit(2), Expr::nat_lit(3));
    let mut state = ProofState::new(env, goal);

    let result = eval_decide(&mut state);
    assert!(result.is_err(), "decide should fail on 2 = 3");
}

// =========================================================================
// Decidable instance resolution
// =========================================================================

#[test]
fn test_decide_with_dec_eq_instance() {
    // Goal: 0 = 0 (with Nat.decEq available via full Decidable init)
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_decidable().unwrap();

    // Add Nat.decEq : (a b : Nat) → Decidable (a = b)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let dec_eq_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat,
                        ),
                        Expr::bvar(1),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.decEq"),
        level_params: vec![],
        type_: dec_eq_ty,
    })
    .unwrap();

    let goal = nat_eq_goal(Expr::nat_lit(0), Expr::nat_lit(0));
    let mut state = ProofState::new(env, goal);

    // Should succeed — either via direct evaluation or Decidable instance
    eval_decide(&mut state).expect("decide should close 0 = 0 with decEq");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_decide_no_goals_fails() {
    let env = Environment::new();
    // Create a state with no goals by closing the only one
    let goal = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, goal);
    state.goals.clear();

    let result = eval_decide(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "decide should fail with NoGoals"
    );
}
