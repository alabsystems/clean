// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IsaSAT refinement formalization.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_isasat_refinement()
        .expect("init_isasat_refinement");
    env
}

#[test]
fn test_cdcl_state_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("IsaSAT.CDCLState"))
        .is_some());
}

#[test]
fn test_all_types_registered() {
    let env = make_env();
    for name in [
        "IsaSAT.CDCLState",
        "IsaSAT.Trail",
        "IsaSAT.ClauseDB",
        "IsaSAT.Conflict",
        "IsaSAT.CDCLTransition",
        "IsaSAT.WatchList",
        "IsaSAT.ConcreteState",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_transition_constructors_registered() {
    let env = make_env();
    for ctor in [
        "Propagate",
        "Decide",
        "Conflict",
        "Learn",
        "Forget",
        "Restart",
        "Backtrack",
    ] {
        let name = format!("IsaSAT.CDCLTransition.{ctor}");
        assert!(
            env.get_const(&Name::from_string(&name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_functions_registered() {
    let env = make_env();
    for name in [
        "IsaSAT.cdcl_step",
        "IsaSAT.cdcl_invariant",
        "IsaSAT.trail_consistent",
        "IsaSAT.all_propagated",
        "IsaSAT.trail_of",
        "IsaSAT.refinement_relation",
        "IsaSAT.abstract_of",
        "IsaSAT.concrete_propagate",
        "IsaSAT.ConcreteState.watch_list",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "IsaSAT.invariant_preserved_by_propagate",
        "IsaSAT.invariant_preserved_by_decide",
        "IsaSAT.invariant_preserved_by_backtrack",
        "IsaSAT.refinement_simulation_propagate",
        "IsaSAT.refinement_preserves_invariant",
        "IsaSAT.trail_consistency_preserved",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "IsaSAT.invariant_preserved_by_propagate_helper",
        "IsaSAT.invariant_preserved_by_decide_helper",
        "IsaSAT.invariant_preserved_by_backtrack_helper",
        "IsaSAT.refinement_simulation_propagate_helper",
        "IsaSAT.refinement_preserves_invariant_helper",
        "IsaSAT.trail_consistency_preserved_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_cdcl_state_type_checks() {
    let env = make_env();
    let state = crate::expr::Expr::const_(Name::from_string("IsaSAT.CDCLState"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&state).expect("infer IsaSAT.CDCLState type");
    // CDCLState : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_cdcl_step_type_checks() {
    let env = make_env();
    let step = crate::expr::Expr::const_(Name::from_string("IsaSAT.cdcl_step"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&step).expect("infer IsaSAT.cdcl_step type");
    // cdcl_step : CDCLState -> CDCLTransition -> CDCLState
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_refinement_relation_type_checks() {
    let env = make_env();
    let rel = crate::expr::Expr::const_(Name::from_string("IsaSAT.refinement_relation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rel)
        .expect("infer IsaSAT.refinement_relation type");
    // refinement_relation : CDCLState -> ConcreteState -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_invariant_type_checks() {
    let env = make_env();
    let inv = crate::expr::Expr::const_(Name::from_string("IsaSAT.cdcl_invariant"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&inv)
        .expect("infer IsaSAT.cdcl_invariant type");
    // cdcl_invariant : CDCLState -> ClauseDB -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_of_type_checks() {
    let env = make_env();
    let abs = crate::expr::Expr::const_(Name::from_string("IsaSAT.abstract_of"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&abs).expect("infer IsaSAT.abstract_of type");
    // abstract_of : ConcreteState -> CDCLState
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_concrete_propagate_type_checks() {
    let env = make_env();
    let cp = crate::expr::Expr::const_(Name::from_string("IsaSAT.concrete_propagate"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cp)
        .expect("infer IsaSAT.concrete_propagate type");
    // concrete_propagate : ConcreteState -> ConcreteState
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent_init() {
    let mut env = Environment::new();
    env.init_isasat_refinement()
        .expect("first init_isasat_refinement");
    env.init_isasat_refinement()
        .expect("second init_isasat_refinement should be idempotent");
}
