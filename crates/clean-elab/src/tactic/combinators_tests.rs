// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the tactic combinator framework (`combinators.rs`).

use super::combinators::{
    eval_all_goals, eval_any_goals, eval_first, eval_focus, eval_repeat, eval_rotate, eval_swap,
    eval_try, CombinatorConfig, TacticCtx,
};
use super::core::{Goal, ProofState, TacticError, TacticResult};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

/// Helper: build a minimal environment with types A, B, C and a proof `a : A`.
fn setup_env() -> Environment {
    let mut env = Environment::new();
    for name in ["A", "B", "C"] {
        env.add_decl(clean_kernel::env::Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
    }
    env.add_decl(clean_kernel::env::Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();
    env
}

/// Helper: build a multi-goal proof state with goals of type A, B, C.
fn multi_goal_state(env: Environment) -> ProofState {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let meta_b = ps.metas_mut().fresh(b.clone());
    let meta_c = ps.metas_mut().fresh(c.clone());
    ps.goals.push_back(Goal {
        meta_id: meta_b,
        target: b,
        local_ctx: vec![],
        tag: Some("goal_B".into()),
    });
    ps.goals.push_back(Goal {
        meta_id: meta_c,
        target: c,
        local_ctx: vec![],
        tag: Some("goal_C".into()),
    });
    ps
}

/// A tactic that always succeeds (no-op).
fn succeed_tactic(ctx: &mut TacticCtx) -> TacticResult {
    let _ = ctx;
    Ok(())
}

/// A tactic that always fails.
fn fail_tactic(ctx: &mut TacticCtx) -> TacticResult {
    let _ = ctx;
    Err(TacticError::NoProgress {
        tactic: "fail".into(),
    })
}

/// A tactic that closes the current goal by assigning it a dummy proof.
fn close_current_goal(ctx: &mut TacticCtx) -> TacticResult {
    let goal = ctx.state.current_goal().ok_or(TacticError::NoGoals)?;
    let meta_id = goal.meta_id;
    let target = goal.target.clone();
    // Assign a sorry-like term (just use the target as a self-reference for testing)
    ctx.state.metas_mut().assign(meta_id, target);
    ctx.state.pop_current_goal()?;
    Ok(())
}

// ===== eval_repeat tests =====

#[test]
fn test_repeat_stops_after_max_iterations() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let config = CombinatorConfig { max_repeat: 3 };
    let mut ctx = TacticCtx::with_config(&mut ps, config);

    // Track invocations via a side channel: we use succeed_tactic which is a no-op,
    // so repeat runs it max_repeat times then stops (since it never fails).
    let result = eval_repeat(succeed_tactic, None, &mut ctx);
    assert!(result.is_ok(), "repeat should always succeed");
    // State should be unchanged (succeed is a no-op)
    assert!(!ctx.state.is_complete());
}

#[test]
fn test_repeat_with_explicit_max() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_repeat(succeed_tactic, Some(5), &mut ctx);
    assert!(result.is_ok());
}

#[test]
fn test_repeat_stops_on_failure() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    // fail_tactic fails immediately, so repeat runs 0 iterations and succeeds
    let result = eval_repeat(fail_tactic, None, &mut ctx);
    assert!(
        result.is_ok(),
        "repeat should succeed even when tactic fails immediately"
    );
}

#[test]
fn test_repeat_stops_when_goals_complete() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    // close_current_goal closes the only goal, so repeat stops after 1 iteration
    let result = eval_repeat(close_current_goal, None, &mut ctx);
    assert!(result.is_ok());
    assert!(
        ctx.state.is_complete(),
        "proof should be complete after closing only goal"
    );
}

// ===== eval_first tests =====

#[test]
fn test_first_picks_first_succeeding_tactic() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let tactics: &[fn(&mut TacticCtx) -> TacticResult] =
        &[fail_tactic, fail_tactic, succeed_tactic, fail_tactic];
    let result = eval_first(tactics, &mut ctx);
    assert!(result.is_ok(), "first should succeed on third tactic");
}

#[test]
fn test_first_fails_when_all_fail() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let tactics: &[fn(&mut TacticCtx) -> TacticResult] = &[fail_tactic];
    let result = eval_first(tactics, &mut ctx);
    // Last tactic's error propagates directly
    assert!(result.is_err());
}

#[test]
fn test_first_empty_list_fails() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let tactics: &[fn(&mut TacticCtx) -> TacticResult] = &[];
    let result = eval_first(tactics, &mut ctx);
    assert!(matches!(result, Err(TacticError::AllTacticsFailed { .. })));
}

// ===== eval_try tests =====

#[test]
fn test_try_ignores_failure() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_try(fail_tactic, &mut ctx);
    assert!(result.is_ok(), "try should always succeed");
    assert!(
        !ctx.state.is_complete(),
        "state should be unchanged after failed try"
    );
}

#[test]
fn test_try_preserves_success() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_try(close_current_goal, &mut ctx);
    assert!(result.is_ok());
    assert!(
        ctx.state.is_complete(),
        "try should preserve successful tactic state"
    );
}

// ===== eval_all_goals tests =====

#[test]
fn test_all_goals_applies_to_each_goal() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_all_goals(close_current_goal, &mut ctx);
    assert!(result.is_ok());
    assert!(ctx.state.is_complete(), "all goals should be closed");
}

#[test]
fn test_all_goals_fails_on_first_failure() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_all_goals(fail_tactic, &mut ctx);
    assert!(
        result.is_err(),
        "all_goals should fail when tactic fails on first goal"
    );
}

// ===== eval_any_goals tests =====

#[test]
fn test_any_goals_partial_success() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let initial_count = ps.goals.len();
    assert_eq!(initial_count, 3);

    // Use succeed_tactic which is a no-op — it succeeds on all goals
    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_any_goals(succeed_tactic, &mut ctx);
    assert!(
        result.is_ok(),
        "any_goals should succeed if at least one goal succeeds"
    );
}

#[test]
fn test_any_goals_all_fail() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_any_goals(fail_tactic, &mut ctx);
    assert!(
        matches!(result, Err(TacticError::AllTacticsFailed { .. })),
        "any_goals should fail when all goals fail"
    );
}

// ===== eval_focus tests =====

#[test]
fn test_focus_on_specific_goal_index() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    // Focus on goal at index 1 (B) and close it
    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus(close_current_goal, 1, &mut ctx);
    assert!(result.is_ok());
    // Should have 2 remaining goals (A and C)
    assert_eq!(ctx.state.goals.len(), 2);
}

#[test]
fn test_focus_on_first_goal() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus(close_current_goal, 0, &mut ctx);
    assert!(result.is_ok());
    assert_eq!(ctx.state.goals.len(), 2);
}

#[test]
fn test_focus_out_of_bounds() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus(succeed_tactic, 10, &mut ctx);
    assert!(
        matches!(result, Err(TacticError::InvalidTarget { .. })),
        "focus should fail on out-of-bounds index"
    );
}

// ===== eval_rotate tests =====

#[test]
fn test_rotate_forward() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    // Goals: [A, B, C]
    let tag_0 = ps.goals[0].tag.clone();
    let tag_1 = ps.goals[1].tag.clone();
    let tag_2 = ps.goals[2].tag.clone();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate(1, &mut ctx).unwrap();

    // After rotate(1): [B, C, A]
    assert_eq!(ctx.state.goals[0].tag, tag_1);
    assert_eq!(ctx.state.goals[1].tag, tag_2);
    assert_eq!(ctx.state.goals[2].tag, tag_0);
}

#[test]
fn test_rotate_backward() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    // Goals: [A, B, C]  — goal A has tag None, B has "goal_B", C has "goal_C"
    let tag_0 = ps.goals[0].tag.clone();
    let tag_1 = ps.goals[1].tag.clone();
    let tag_2 = ps.goals[2].tag.clone();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate(-1, &mut ctx).unwrap();

    // After rotate(-1): [C, A, B]
    assert_eq!(ctx.state.goals[0].tag, tag_2);
    assert_eq!(ctx.state.goals[1].tag, tag_0);
    assert_eq!(ctx.state.goals[2].tag, tag_1);
}

#[test]
fn test_rotate_zero_is_noop() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate(0, &mut ctx).unwrap();

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after);
}

#[test]
fn test_rotate_full_cycle() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    // Rotate by the number of goals = full cycle = no-op
    eval_rotate(3, &mut ctx).unwrap();

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after);
}

#[test]
fn test_rotate_empty_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    ps.clear_goals();

    let mut ctx = TacticCtx::new(&mut ps);
    // rotate(0) on empty is OK
    assert!(eval_rotate(0, &mut ctx).is_ok());
    // rotate(1) on empty is NoGoals
    assert!(eval_rotate(1, &mut ctx).is_err());
}

// ===== eval_swap tests =====

#[test]
fn test_swap_first_two_goals() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tag_0 = ps.goals[0].tag.clone();
    let tag_1 = ps.goals[1].tag.clone();
    let tag_2 = ps.goals[2].tag.clone();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_swap(&mut ctx).unwrap();

    assert_eq!(ctx.state.goals[0].tag, tag_1);
    assert_eq!(ctx.state.goals[1].tag, tag_0);
    assert_eq!(ctx.state.goals[2].tag, tag_2);
}

#[test]
fn test_swap_requires_two_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_swap(&mut ctx);
    assert!(
        matches!(result, Err(TacticError::InvalidTarget { .. })),
        "swap should fail with fewer than 2 goals"
    );
}

// ===== CombinatorConfig tests =====

#[test]
fn test_config_default() {
    let config = CombinatorConfig::default();
    assert_eq!(config.max_repeat, 100);
}

#[test]
fn test_config_custom_max_repeat() {
    let config = CombinatorConfig { max_repeat: 50 };
    assert_eq!(config.max_repeat, 50);
}
