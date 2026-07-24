// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended tactic combinators (`combinators_ext.rs`).

use super::combinators::{CombinatorConfig, TacticCtx};
use super::combinators_ext::{
    eval_and_then, eval_focus_and_done, eval_repeat1, eval_rotate_left, eval_rotate_right, eval_seq,
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
    ctx.state.metas_mut().assign(meta_id, target);
    ctx.state.pop_current_goal()?;
    Ok(())
}

/// A tactic that splits the current goal into two subgoals.
/// Closes the current goal and pushes two new goals to the front.
fn split_tactic(ctx: &mut TacticCtx) -> TacticResult {
    let goal = ctx.state.current_goal().ok_or(TacticError::NoGoals)?;
    let meta_id = goal.meta_id;
    let target = goal.target.clone();

    // Create two new subgoals with the same target type
    let sub1 = ctx.state.metas_mut().fresh(target.clone());
    let sub2 = ctx.state.metas_mut().fresh(target.clone());

    // Assign the original goal (pretend we proved it via the subgoals)
    ctx.state.metas_mut().assign(meta_id, target.clone());
    ctx.state.pop_current_goal()?;

    // Push two new subgoals at the front
    ctx.state.goals.push_front(Goal {
        meta_id: sub2,
        target: target.clone(),
        local_ctx: vec![],
        tag: Some("split_2".into()),
    });
    ctx.state.goals.push_front(Goal {
        meta_id: sub1,
        target,
        local_ctx: vec![],
        tag: Some("split_1".into()),
    });

    Ok(())
}

// ===== eval_repeat1 tests =====

#[test]
fn test_repeat1_succeeds_when_tactic_succeeds_once() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    // close_current_goal succeeds on the only goal, repeat1 succeeds
    let result = eval_repeat1(close_current_goal, None, &mut ctx);
    assert!(result.is_ok());
    assert!(ctx.state.is_complete());
}

#[test]
fn test_repeat1_fails_when_first_application_fails() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_repeat1(fail_tactic, None, &mut ctx);
    assert!(
        result.is_err(),
        "repeat1 should fail when first application fails"
    );
    // State should be unchanged
    assert!(!ctx.state.is_complete());
    assert_eq!(ctx.state.goals.len(), 1);
}

#[test]
fn test_repeat1_continues_until_failure() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    // close_current_goal closes one goal at a time; repeat1 closes all 3
    let result = eval_repeat1(close_current_goal, None, &mut ctx);
    assert!(result.is_ok());
    assert!(ctx.state.is_complete());
}

#[test]
fn test_repeat1_respects_max_limit() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    // max=2 means at most 2 applications (closes 2 of 3 goals)
    let result = eval_repeat1(close_current_goal, Some(2), &mut ctx);
    assert!(result.is_ok());
    assert_eq!(
        ctx.state.goals.len(),
        1,
        "should have 1 goal remaining after max=2"
    );
}

#[test]
fn test_repeat1_with_noop_stops_at_config_limit() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let config = CombinatorConfig { max_repeat: 5 };
    let mut ctx = TacticCtx::with_config(&mut ps, config);
    // succeed_tactic is a no-op: repeat1 runs it max_repeat times
    let result = eval_repeat1(succeed_tactic, None, &mut ctx);
    assert!(result.is_ok());
}

// ===== eval_seq tests =====

#[test]
fn test_seq_both_succeed() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_seq(succeed_tactic, succeed_tactic, &mut ctx);
    assert!(result.is_ok());
}

#[test]
fn test_seq_first_fails_rolls_back() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    let goal_count_before = ps.goals.len();

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_seq(fail_tactic, succeed_tactic, &mut ctx);
    assert!(result.is_err());
    assert_eq!(
        ctx.state.goals.len(),
        goal_count_before,
        "state should be restored"
    );
}

#[test]
fn test_seq_second_fails_rolls_back() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let goal_count_before = ps.goals.len();

    let mut ctx = TacticCtx::new(&mut ps);
    // close_current_goal succeeds, then fail_tactic fails — both rolled back
    let result = eval_seq(close_current_goal, fail_tactic, &mut ctx);
    assert!(result.is_err());
    assert_eq!(
        ctx.state.goals.len(),
        goal_count_before,
        "state should be fully restored"
    );
}

#[test]
fn test_seq_close_then_close() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_seq(close_current_goal, close_current_goal, &mut ctx);
    assert!(result.is_ok());
    assert_eq!(ctx.state.goals.len(), 1, "two goals should be closed");
}

// ===== eval_and_then tests =====

#[test]
fn test_and_then_tac1_splits_tac2_closes() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    assert_eq!(ps.goals.len(), 1);

    let mut ctx = TacticCtx::new(&mut ps);
    // split_tactic creates 2 subgoals, close_current_goal closes each
    let result = eval_and_then(split_tactic, close_current_goal, &mut ctx);
    assert!(result.is_ok());
    assert!(ctx.state.is_complete(), "all subgoals should be closed");
}

#[test]
fn test_and_then_tac1_fails() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    let goal_count_before = ps.goals.len();

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_and_then(fail_tactic, succeed_tactic, &mut ctx);
    assert!(result.is_err());
    assert_eq!(ctx.state.goals.len(), goal_count_before);
}

#[test]
fn test_and_then_tac2_fails_rolls_back() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    let goal_count_before = ps.goals.len();

    let mut ctx = TacticCtx::new(&mut ps);
    // split_tactic creates 2 subgoals, fail_tactic fails on the first
    let result = eval_and_then(split_tactic, fail_tactic, &mut ctx);
    assert!(result.is_err());
    assert_eq!(
        ctx.state.goals.len(),
        goal_count_before,
        "state should be fully restored"
    );
}

#[test]
fn test_and_then_preserves_remaining_goals() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    // Goals: [A, B, C]
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    // succeed_tactic on goal A (no-op), then succeed on its "result" (no-op)
    let result = eval_and_then(succeed_tactic, succeed_tactic, &mut ctx);
    assert!(result.is_ok());
    // All 3 goals should remain (succeed is no-op)
    assert_eq!(ctx.state.goals.len(), 3);
}

// ===== eval_focus_and_done tests =====

#[test]
fn test_focus_and_done_succeeds_when_goal_closed() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    assert_eq!(ps.goals.len(), 3);

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus_and_done(close_current_goal, &mut ctx);
    assert!(result.is_ok());
    // 2 remaining goals (B and C)
    assert_eq!(ctx.state.goals.len(), 2);
}

#[test]
fn test_focus_and_done_fails_when_subgoals_remain() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    // split_tactic creates 2 subgoals instead of closing, so focus_and_done fails
    let result = eval_focus_and_done(split_tactic, &mut ctx);
    assert!(
        matches!(result, Err(TacticError::UnsolvedGoals { count: 2, .. })),
        "should report 2 unsolved subgoals, got: {result:?}"
    );
}

#[test]
fn test_focus_and_done_fails_when_tactic_fails() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let goal_count_before = ps.goals.len();

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus_and_done(fail_tactic, &mut ctx);
    assert!(result.is_err());
    // Goals should be restored
    assert_eq!(ctx.state.goals.len(), goal_count_before);
}

#[test]
fn test_focus_and_done_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    ps.clear_goals();

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_focus_and_done(succeed_tactic, &mut ctx);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_focus_and_done_noop_leaves_goal_unsolved() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);

    let mut ctx = TacticCtx::new(&mut ps);
    // succeed_tactic is a no-op — the goal is not closed
    let result = eval_focus_and_done(succeed_tactic, &mut ctx);
    assert!(
        matches!(result, Err(TacticError::UnsolvedGoals { count: 1, .. })),
        "no-op should leave 1 unsolved goal, got: {result:?}"
    );
}

// ===== eval_rotate_left / eval_rotate_right tests =====

#[test]
fn test_rotate_left_by_one() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    // Goals: [A(None), B("goal_B"), C("goal_C")]
    let tag_0 = ps.goals[0].tag.clone();
    let tag_1 = ps.goals[1].tag.clone();
    let tag_2 = ps.goals[2].tag.clone();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_left(1, &mut ctx).expect("rotate_left should succeed");

    // After rotate_left(1): [B, C, A]
    assert_eq!(ctx.state.goals[0].tag, tag_1);
    assert_eq!(ctx.state.goals[1].tag, tag_2);
    assert_eq!(ctx.state.goals[2].tag, tag_0);
}

#[test]
fn test_rotate_right_by_one() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tag_0 = ps.goals[0].tag.clone();
    let tag_1 = ps.goals[1].tag.clone();
    let tag_2 = ps.goals[2].tag.clone();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_right(1, &mut ctx).expect("rotate_right should succeed");

    // After rotate_right(1): [C, A, B]
    assert_eq!(ctx.state.goals[0].tag, tag_2);
    assert_eq!(ctx.state.goals[1].tag, tag_0);
    assert_eq!(ctx.state.goals[2].tag, tag_1);
}

#[test]
fn test_rotate_left_zero_is_noop() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_left(0, &mut ctx).expect("rotate_left(0) should succeed");

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after);
}

#[test]
fn test_rotate_right_zero_is_noop() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_right(0, &mut ctx).expect("rotate_right(0) should succeed");

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after);
}

#[test]
fn test_rotate_left_full_cycle() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_left(3, &mut ctx).expect("full cycle should succeed");

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after, "full cycle should be a no-op");
}

#[test]
fn test_rotate_right_full_cycle() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_right(3, &mut ctx).expect("full cycle should succeed");

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(tags_before, tags_after, "full cycle should be a no-op");
}

#[test]
fn test_rotate_left_right_inverse() {
    let env = setup_env();
    let mut ps = multi_goal_state(env);
    let tags_before: Vec<_> = ps.goals.iter().map(|g| g.tag.clone()).collect();

    let mut ctx = TacticCtx::new(&mut ps);
    eval_rotate_left(2, &mut ctx).expect("rotate_left should succeed");
    eval_rotate_right(2, &mut ctx).expect("rotate_right should succeed");

    let tags_after: Vec<_> = ctx.state.goals.iter().map(|g| g.tag.clone()).collect();
    assert_eq!(
        tags_before, tags_after,
        "left then right by same amount should be identity"
    );
}

#[test]
fn test_rotate_left_empty_goals_nonzero() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a);
    ps.clear_goals();

    let mut ctx = TacticCtx::new(&mut ps);
    let result = eval_rotate_left(1, &mut ctx);
    assert!(result.is_err(), "rotate_left on empty goals should fail");
}
