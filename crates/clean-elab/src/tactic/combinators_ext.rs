// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tactic combinators — additional composition primitives.
//!
//! Builds on the function-pointer-based [`TacticFn`] API from [`combinators`]
//! to provide:
//! - [`eval_repeat1`] — apply at least once (fails if first application fails)
//! - [`eval_seq`] — sequence two tactics
//! - [`eval_and_then`] — apply tac1, then tac2 to every resulting goal
//! - [`eval_focus_and_done`] — focus on first goal and require it to be closed
//! - [`eval_rotate_left`] / [`eval_rotate_right`] — named rotation directions
//!
//! # Design
//!
//! These combinators complement the base set in [`combinators`]. They follow
//! the same conventions: function pointers for zero-allocation composition,
//! scoped meta rollback for failure recovery, and `TacticResult` return types.

use super::combinators::{eval_repeat, eval_rotate, TacticCtx, TacticFn};
use super::core::{TacticError, TacticResult};

/// Apply a tactic at least once, then repeat until failure.
///
/// Unlike [`eval_repeat`], this combinator fails if the very first application
/// of `tac` fails. After a successful first application, it behaves identically
/// to `eval_repeat` — continuing until failure or the iteration limit.
///
/// # Contract
///
/// REQUIRES: `ctx.state` has a valid meta scope stack
/// ENSURES: on `Ok`, tactic was applied at least once
/// ENSURES: on `Err`, tactic failed on the first application; state is restored
///
/// # Example
/// ```text
/// eval_repeat1(intro_tactic, None, &mut ctx)  // at least one intro
/// ```
pub(crate) fn eval_repeat1(tac: TacticFn, max: Option<usize>, ctx: &mut TacticCtx) -> TacticResult {
    // First application must succeed
    let saved_goals = ctx.state.goals.clone();
    ctx.state.metas_mut().push_scope();

    match tac(ctx) {
        Ok(()) => {
            ctx.state.metas_mut().commit();
        }
        Err(err) => {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            return Err(err);
        }
    }

    // If first succeeded, continue with eval_repeat for remaining iterations
    if !ctx.state.is_complete() {
        let remaining = max.map(|m| m.saturating_sub(1));
        eval_repeat(tac, remaining, ctx)?;
    }

    Ok(())
}

/// Sequence two tactics: apply `tac1`, then apply `tac2`.
///
/// If `tac1` fails, `tac2` is not attempted and the error propagates.
/// If `tac1` succeeds but `tac2` fails, both are rolled back.
///
/// # Contract
///
/// REQUIRES: `ctx.state` has a valid meta scope stack
/// ENSURES: on `Ok`, both `tac1` and `tac2` succeeded
/// ENSURES: on `Err`, state is restored to pre-call
pub(crate) fn eval_seq(tac1: TacticFn, tac2: TacticFn, ctx: &mut TacticCtx) -> TacticResult {
    let saved_goals = ctx.state.goals.clone();
    ctx.state.metas_mut().push_scope();

    match tac1(ctx) {
        Ok(()) => {}
        Err(err) => {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            return Err(err);
        }
    }

    match tac2(ctx) {
        Ok(()) => {
            ctx.state.metas_mut().commit();
            Ok(())
        }
        Err(err) => {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            Err(err)
        }
    }
}

/// Apply `tac1`, then apply `tac2` to every goal that `tac1` produced.
///
/// This implements Lean 4's `<;>` semicolon combinator semantics:
/// run `tac1` on the current goal, then run `tac2` on each new goal
/// that `tac1` created.
///
/// # Contract
///
/// REQUIRES: `ctx.state` has a valid meta scope stack
/// ENSURES: on `Ok`, `tac1` succeeded on the original goal, and `tac2`
///   succeeded on every goal that `tac1` produced
/// ENSURES: on `Err` from `tac1`, state is fully restored
/// ENSURES: on `Err` from `tac2`, state is fully restored
pub(crate) fn eval_and_then(tac1: TacticFn, tac2: TacticFn, ctx: &mut TacticCtx) -> TacticResult {
    let saved_goals = ctx.state.goals.clone();
    let original_count = ctx.state.goals.len();
    ctx.state.metas_mut().push_scope();

    match tac1(ctx) {
        Ok(()) => {}
        Err(err) => {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            return Err(err);
        }
    }

    // tac1 consumed some goals and may have produced new ones.
    // The new goals produced by tac1 are at the front of the deque
    // (replacing the consumed goal). Goals that were after the consumed
    // goal remain at the back. We need to apply tac2 to all current
    // goals that were not in the original tail.
    //
    // After tac1: goals = [new_from_tac1..., remaining_original...]
    // We want to apply tac2 to the new goals from tac1.
    let current_count = ctx.state.goals.len();
    // original_count - 1 = goals that were after the consumed goal (the tail)
    // current_count - (original_count - 1) = number of new goals from tac1
    let tail_count = original_count.saturating_sub(1);
    let new_goal_count = current_count.saturating_sub(tail_count);

    for _ in 0..new_goal_count {
        if ctx.state.goals.is_empty() {
            break;
        }
        match tac2(ctx) {
            Ok(()) => {}
            Err(err) => {
                ctx.state.invalidate_tc_cache();
                ctx.state.goals = saved_goals;
                ctx.state.metas_mut().pop_scope();
                return Err(err);
            }
        }
    }

    ctx.state.metas_mut().commit();
    Ok(())
}

/// Focus on the first goal, apply a tactic, and require the goal to be closed.
///
/// This implements Lean 4's `focusAndDone` semantics: isolate goal 0,
/// run the tactic, then check that zero unsolved goals remain in the
/// focused scope. If any subgoals remain, returns `UnsolvedGoals`.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// ENSURES: on `Ok`, the focused goal and all its subgoals are closed;
///   remaining goals (index 1..) are restored
/// ENSURES: on `Err(NoGoals)`, no goals were available
/// ENSURES: on `Err(UnsolvedGoals)`, remaining goals are still restored
pub(crate) fn eval_focus_and_done(tac: TacticFn, ctx: &mut TacticCtx) -> TacticResult {
    if ctx.state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Isolate the first goal
    let rest = ctx.state.goals.split_off(1);

    let result = tac(ctx);

    if let Err(err) = result {
        ctx.state.goals.extend(rest);
        return Err(err);
    }

    // Check that all focused goals are closed
    if !ctx.state.goals.is_empty() {
        let remaining = ctx.state.goals.len();
        ctx.state.goals.extend(rest);
        return Err(TacticError::UnsolvedGoals {
            count: remaining,
            detail: String::new(),
        });
    }

    // Restore the rest of the goals
    ctx.state.goals.extend(rest);
    Ok(())
}

/// Rotate goals left by `n` positions (front goals move to back).
///
/// Convenience wrapper for `eval_rotate(n as isize, ctx)`.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty (for non-zero `n`)
/// ENSURES: goals are cyclically permuted left by `n` positions
pub(crate) fn eval_rotate_left(n: usize, ctx: &mut TacticCtx) -> TacticResult {
    eval_rotate(n as isize, ctx)
}

/// Rotate goals right by `n` positions (back goals move to front).
///
/// Convenience wrapper for `eval_rotate(-(n as isize), ctx)`.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty (for non-zero `n`)
/// ENSURES: goals are cyclically permuted right by `n` positions
pub(crate) fn eval_rotate_right(n: usize, ctx: &mut TacticCtx) -> TacticResult {
    eval_rotate(-(n as isize), ctx)
}
