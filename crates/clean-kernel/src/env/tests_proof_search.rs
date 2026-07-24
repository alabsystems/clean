// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `env::proof_search` module.

use crate::env::proof_search::{
    mk_eq_refl, parse_eq_goal, search_proof, try_verify_proof, ProofSearchResult,
};
use crate::env::types::{ConstantKind, Declaration};
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    env.init_true_false().unwrap();
    env
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}

fn nat_succ(arg: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), arg)
}

fn eq_level() -> Level {
    Level::succ(Level::zero())
}

fn eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![eq_level()]),
        [nat(), lhs, rhs],
    )
}

fn assert_const_head(expr: &Expr, expected: &str) {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), expected),
        other => panic!("expected const head {expected}, got {other:?}"),
    }
}

#[test]
fn test_parse_eq_goal_nat_eq_returns_components() {
    let goal = eq_goal(nat_zero(), nat_zero());
    let (ty, levels, lhs, rhs) = parse_eq_goal(&goal).unwrap();

    assert_eq!(ty, nat());
    assert_eq!(levels, vec![eq_level()]);
    assert_eq!(lhs, nat_zero());
    assert_eq!(rhs, nat_zero());
}

#[test]
fn test_parse_eq_goal_not_eq_returns_none() {
    assert!(parse_eq_goal(&Expr::const_str("Nat")).is_none());
}

#[test]
fn test_mk_eq_refl_nat_zero_type_checks() {
    let env = make_env();
    let proof = mk_eq_refl(&[eq_level()], &nat(), &nat_zero());
    let goal = eq_goal(nat_zero(), nat_zero());
    let tc = TypeChecker::new(&env);
    let proof_ty = tc.infer_type(&proof).unwrap();

    assert!(tc.is_def_eq(&proof_ty, &goal));
}

#[test]
fn test_search_proof_refl_nat_zero_returns_found() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_zero());

    match search_proof(&env, &goal, 8) {
        ProofSearchResult::Found { proof, .. } => {
            assert_const_head(&proof, "Eq.refl");
            assert!(try_verify_proof(&env, &goal, &proof));
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn test_search_proof_refl_succ_returns_found() {
    let env = make_env();
    let succ_zero = nat_succ(nat_zero());
    let goal = eq_goal(succ_zero.clone(), succ_zero);

    match search_proof(&env, &goal, 8) {
        ProofSearchResult::Found { proof, .. } => {
            assert_const_head(&proof, "Eq.refl");
            assert!(try_verify_proof(&env, &goal, &proof));
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn test_search_proof_not_equal_returns_exhausted() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_succ(nat_zero()));
    let budget = env.constants().count() + 2;

    match search_proof(&env, &goal, budget) {
        ProofSearchResult::Exhausted { candidates_tried } => {
            assert_eq!(candidates_tried, budget);
        }
        other => panic!("expected Exhausted, got {other:?}"),
    }
}

#[test]
fn test_search_proof_true_returns_found() {
    let env = make_env();
    let goal = Expr::const_str("True");

    match search_proof(&env, &goal, 8) {
        ProofSearchResult::Found { proof, strategy } => {
            assert_eq!(proof, Expr::const_str("True.intro"));
            assert_eq!(strategy, "trivial_prop");
            assert!(try_verify_proof(&env, &goal, &proof));
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn test_try_verify_proof_valid_returns_true() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_zero());
    let proof = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![eq_level()]),
        [nat(), nat_zero()],
    );

    assert!(try_verify_proof(&env, &goal, &proof));
}

#[test]
fn test_try_verify_proof_invalid_returns_false() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_zero());

    assert!(!try_verify_proof(
        &env,
        &goal,
        &Expr::const_str("True.intro")
    ));
}

#[test]
fn test_search_proof_budget_zero_returns_budget_exceeded() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_zero());

    match search_proof(&env, &goal, 0) {
        ProofSearchResult::BudgetExceeded {
            candidates_tried,
            budget,
        } => {
            assert_eq!(candidates_tried, 0);
            assert_eq!(budget, 0);
        }
        other => panic!("expected BudgetExceeded, got {other:?}"),
    }
}

#[test]
fn test_search_proof_existing_decl_returns_lookup() {
    let mut env = make_env();
    let axiom_name = Name::from_string("ProofSearch.customFalse");
    env.add_decl(Declaration::Axiom {
        name: axiom_name.clone(),
        level_params: vec![],
        type_: Expr::const_str("False"),
    })
    .unwrap();

    let info = env.get_const(&axiom_name).unwrap();
    assert_eq!(info.kind, ConstantKind::Axiom);

    match search_proof(&env, &Expr::const_str("False"), 128) {
        ProofSearchResult::Found { proof, strategy } => {
            assert_eq!(proof, Expr::const_(axiom_name, vec![]));
            assert_eq!(strategy, "lookup");
        }
        other => panic!("expected Found, got {other:?}"),
    }
}
