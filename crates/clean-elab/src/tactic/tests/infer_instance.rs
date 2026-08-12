// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the registry-wired `infer_instance` tactic.
//!
//! `infer_instance` synthesizes a type-class instance for the goal and closes
//! it via the kernel-checked `exact`. These tests drive the full
//! `SurfaceTactic::Named { name: "infer_instance" }` dispatch path through
//! `ElabCtx::eval` so the registry wiring (parser-visible pattern + handler)
//! and the kernel acceptance of the synthesized term are both exercised.

use super::*;
use crate::infer::ElabCtx;
use crate::tactic::registry::{TacticArgPattern, TacticEval, TacticRegistry};
use clean_kernel::{BinderInfo, Name};
use clean_parser::{Span, SurfaceTactic};

/// A nullary `SurfaceTactic::Named` node, the shape the parser produces for a
/// bare `infer_instance` invocation.
fn infer_instance_tactic() -> SurfaceTactic {
    SurfaceTactic::Named {
        span: Span::dummy(),
        name: "infer_instance".to_string(),
        args: vec![],
    }
}

/// Environment with `Decidable`, `True`/`False`, `Eq`, and classical axioms.
fn setup_env_decidable() -> Environment {
    let mut env = Environment::new();
    env.init_decidable().expect("init Decidable");
    env.init_eq().expect("init Eq");
    env.init_classical().expect("init classical");
    env
}

// ---------------------------------------------------------------------------
// Registry wiring
// ---------------------------------------------------------------------------

#[test]
fn test_infer_instance_registered_as_nullary() {
    let mut registry = TacticRegistry::new();
    builtins::register_builtin_tactics(&mut registry);

    let entry = registry
        .get("infer_instance")
        .expect("infer_instance should be a registered simple tactic");
    assert_eq!(
        entry.pattern,
        TacticArgPattern::Nullary,
        "infer_instance takes no arguments, so it must use the Nullary pattern"
    );
}

// ---------------------------------------------------------------------------
// Kernel-accepted success
// ---------------------------------------------------------------------------

#[test]
fn test_infer_instance_closes_decidable_true_with_checked_proof() {
    let env = setup_env_decidable();
    // Goal: `Decidable True`.
    let target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let mut state = ProofState::new(env.clone(), target.clone());

    let mut ctx = ElabCtx::new(&env);
    ctx.eval(&mut state, &infer_instance_tactic())
        .expect("infer_instance should synthesize a `Decidable True` instance");

    assert!(
        state.is_complete(),
        "infer_instance should close the `Decidable True` goal"
    );

    // The closing term must type-check against the original goal in the kernel.
    let proof = state
        .closed_proof()
        .expect("a closed goal must carry a proof term");
    TypeChecker::new(&env)
        .check_type(&proof, &target)
        .expect("synthesized `Decidable True` instance must type-check in the kernel");
}

// ---------------------------------------------------------------------------
// Misuse → TacticError (never panic), goal untouched
// ---------------------------------------------------------------------------

#[test]
fn test_infer_instance_non_class_goal_errors_and_preserves_goal() {
    let env = setup_env_decidable();
    // `True → True` is a Pi, not a type-class application, so there is no class
    // name to synthesize for.
    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let target = Expr::pi(BinderInfo::Default, true_ty.clone(), true_ty);
    let mut state = ProofState::new(env.clone(), target);

    let mut ctx = ElabCtx::new(&env);
    let err = ctx
        .eval(&mut state, &infer_instance_tactic())
        .expect_err("infer_instance on a non-class goal should fail, not panic");

    let err_text = format!("{err:?}");
    assert!(
        err_text.contains("type class"),
        "expected a 'not a type class constraint' error, got: {err_text}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "a failed infer_instance must leave the original goal outstanding"
    );
    assert!(
        !state.is_complete(),
        "a failed infer_instance must not close the goal"
    );
}

#[test]
fn test_infer_instance_no_goals_errors() {
    let env = setup_env_decidable();
    let target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let mut state = ProofState::new(env.clone(), target);

    // Drain the only goal by closing it once, then re-running must error rather
    // than fabricate a second proof.
    let mut ctx = ElabCtx::new(&env);
    ctx.eval(&mut state, &infer_instance_tactic())
        .expect("first infer_instance closes the goal");
    assert!(state.is_complete(), "goal should be closed after first run");

    let err = ctx
        .eval(&mut state, &infer_instance_tactic())
        .expect_err("infer_instance with no goals should fail, not panic");
    assert!(
        matches!(err, TacticError::NoGoals),
        "expected NoGoals when no goal remains, got: {err:?}"
    );
}
