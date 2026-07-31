// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic combinator framework — meta-tactics that compose other tactics.
//!
//! Provides a uniform function-pointer-based API for composing tactics:
//! - `eval_repeat` — apply repeatedly until failure or max iterations
//! - `eval_first` — try each tactic, first success wins
//! - `eval_try` — apply tactic, ignore failure
//! - `eval_all_goals` — apply to every goal
//! - `eval_any_goals` — apply to any goal that succeeds
//! - `eval_focus` — focus on goal at index
//! - `eval_rotate` — rotate goals by n positions
//! - `eval_swap` — swap first two goals
//!
//! # Design
//!
//! [`TacticCtx`] wraps a `&mut ProofState` and [`CombinatorConfig`], giving
//! combinators a uniform interface. [`TacticFn`] is a simple function pointer
//! `fn(&mut TacticCtx<'_>) -> TacticResult`, enabling composition without
//! allocation (unlike the closure-based `combinator.rs` API).

use super::core::{ProofState, TacticError, TacticResult};

/// A tactic function pointer that operates on a [`TacticCtx`].
///
/// Using a function pointer rather than a closure allows combinators to
/// be composed without heap allocation. For closures that capture state,
/// callers should use the closure-based API in `combinator.rs` instead.
pub type TacticFn = fn(&mut TacticCtx<'_>) -> TacticResult;

/// Configuration for tactic combinators.
///
/// Controls iteration limits and other combinator behavior.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombinatorConfig {
    /// Maximum iterations for `eval_repeat` (prevents infinite loops).
    pub max_repeat: usize,
}

impl Default for CombinatorConfig {
    fn default() -> Self {
        Self { max_repeat: 100 }
    }
}

/// Tactic execution context.
///
/// Bundles a mutable reference to the proof state with combinator
/// configuration, providing a uniform interface for [`TacticFn`].
pub struct TacticCtx<'a> {
    /// The proof state being transformed.
    pub state: &'a mut ProofState,
    /// Combinator configuration (iteration limits, etc.).
    pub config: CombinatorConfig,
}

impl<'a> TacticCtx<'a> {
    /// Create a new tactic context with default configuration.
    ///
    /// ENSURES: `self.config == CombinatorConfig::default()`
    pub fn new(state: &'a mut ProofState) -> Self {
        Self {
            state,
            config: CombinatorConfig::default(),
        }
    }

    /// Create a new tactic context with explicit configuration.
    pub fn with_config(state: &'a mut ProofState, config: CombinatorConfig) -> Self {
        Self { state, config }
    }
}

/// Apply a tactic repeatedly until it fails or reaches the maximum iteration count.
///
/// Returns `Ok(())` after the last successful application. The state reflects
/// all successful iterations; the failing iteration is rolled back.
///
/// Uses `config.max_repeat` as the iteration limit when `max` is `None`.
///
/// # Contract
///
/// REQUIRES: `ctx.state` has a valid meta scope stack
/// ENSURES: always returns `Ok(())` — state reflects the last successful
///   application; meta scope stack remains balanced
///
/// # Example
/// ```text
/// eval_repeat(intro_tactic, None, &mut ctx)  // introduce all binders
/// ```
pub fn eval_repeat(tac: TacticFn, max: Option<usize>, ctx: &mut TacticCtx<'_>) -> TacticResult {
    let limit = max.unwrap_or(ctx.config.max_repeat);

    for _ in 0..limit {
        let saved_goals = ctx.state.goals.clone();
        ctx.state.metas_mut().push_scope();

        if tac(ctx).is_ok() {
            ctx.state.metas_mut().commit();
            if ctx.state.is_complete() {
                break;
            }
        } else {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            break;
        }
    }

    Ok(())
}

/// Try each tactic in order, returning the result of the first that succeeds.
///
/// If no tactic succeeds, returns `AllTacticsFailed`.
///
/// # Contract
///
/// REQUIRES: `tacs` is non-empty
/// ENSURES: on `Ok`, exactly one tactic succeeded and its state is committed
/// ENSURES: on `Err(AllTacticsFailed)`, state is restored to pre-call
pub fn eval_first(tacs: &[TacticFn], ctx: &mut TacticCtx<'_>) -> TacticResult {
    if tacs.is_empty() {
        return Err(TacticError::AllTacticsFailed {
            combinator: "first".into(),
        });
    }

    let saved_goals = ctx.state.goals.clone();

    for (idx, tac) in tacs.iter().enumerate() {
        // Last tactic runs without backtracking so its error propagates
        if idx + 1 == tacs.len() {
            return tac(ctx);
        }

        ctx.state.metas_mut().push_scope();

        match tac(ctx) {
            Ok(()) => {
                ctx.state.metas_mut().commit();
                return Ok(());
            }
            Err(err) => {
                ctx.state.invalidate_tc_cache();
                ctx.state.goals = saved_goals.clone();
                ctx.state.metas_mut().pop_scope();
                if err.is_recoverable_first_failure() {
                    continue;
                }
                return Err(err);
            }
        }
    }

    Err(TacticError::AllTacticsFailed {
        combinator: "first".into(),
    })
}

/// Apply a tactic, ignoring failure.
///
/// If the tactic succeeds, the state is advanced. If it fails, the state
/// is fully restored and `Ok(())` is returned.
///
/// # Contract
///
/// REQUIRES: `ctx.state` has a valid meta scope stack
/// ENSURES: always returns `Ok(())` — on failure, state is restored
pub fn eval_try(tac: TacticFn, ctx: &mut TacticCtx<'_>) -> TacticResult {
    let saved_goals = ctx.state.goals.clone();
    ctx.state.metas_mut().push_scope();

    if tac(ctx).is_ok() {
        ctx.state.metas_mut().commit();
    } else {
        ctx.state.invalidate_tc_cache();
        ctx.state.goals = saved_goals;
        ctx.state.metas_mut().pop_scope();
    }

    Ok(())
}

/// Apply a tactic to every goal. Fails if any application fails.
///
/// The tactic is applied to each original goal in order. New goals
/// created by the tactic during processing are not re-processed.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty (delegated to inner tactic)
/// ENSURES: on `Ok`, tactic was applied to every original goal
/// ENSURES: on `Err`, partial progress from earlier goals may remain
pub fn eval_all_goals(tac: TacticFn, ctx: &mut TacticCtx<'_>) -> TacticResult {
    let original_count = ctx.state.goals.len();
    let mut processed = 0;

    while processed < original_count && !ctx.state.goals.is_empty() {
        tac(ctx)?;
        processed += 1;
    }

    Ok(())
}

/// Apply a tactic to each goal, succeeding if at least one succeeds.
///
/// Goals where the tactic fails are rotated to the back unchanged.
/// Returns `AllTacticsFailed` only if every goal fails.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// ENSURES: on `Ok`, at least one goal succeeded
/// ENSURES: on `Err(AllTacticsFailed)`, all goals are restored
pub fn eval_any_goals(tac: TacticFn, ctx: &mut TacticCtx<'_>) -> TacticResult {
    let original_count = ctx.state.goals.len();
    let mut processed = 0;
    let mut any_succeeded = false;

    while processed < original_count && !ctx.state.goals.is_empty() {
        let saved_goals = ctx.state.goals.clone();
        ctx.state.metas_mut().push_scope();

        if tac(ctx).is_ok() {
            ctx.state.metas_mut().commit();
            any_succeeded = true;
        } else {
            ctx.state.invalidate_tc_cache();
            ctx.state.goals = saved_goals;
            ctx.state.metas_mut().pop_scope();
            // Skip this goal by rotating it to the back
            if !ctx.state.goals.is_empty() {
                let goal = ctx.state.pop_current_goal()?;
                ctx.state.goals.push_back(goal);
            }
        }

        processed += 1;
    }

    if any_succeeded {
        Ok(())
    } else {
        Err(TacticError::AllTacticsFailed {
            combinator: "any_goals".into(),
        })
    }
}

/// Focus on the goal at `idx` and apply a tactic to it.
///
/// Moves the target goal to the front, applies the tactic in a focused
/// scope (only the target goal is visible), then restores remaining goals.
///
/// # Contract
///
/// REQUIRES: `idx < ctx.state.goals.len()`
/// ENSURES: on `Ok`, remaining goals are preserved after any new goals
/// ENSURES: on `Err(InvalidTarget)`, `idx` is out of bounds; state unchanged
pub fn eval_focus(tac: TacticFn, idx: usize, ctx: &mut TacticCtx<'_>) -> TacticResult {
    let goal_count = ctx.state.goals.len();
    if idx >= goal_count {
        return Err(TacticError::InvalidTarget {
            tactic: "focus".into(),
            detail: format!("index {idx} out of bounds (have {goal_count} goals)"),
        });
    }

    // Move the target goal to position 0
    if idx > 0 {
        ctx.state.invalidate_tc_cache();
        let goal = ctx.state.goals.remove(idx).expect("index checked above");
        ctx.state.goals.push_front(goal);
    }

    // Isolate just the first goal
    let rest = ctx.state.goals.split_off(1);

    let result = tac(ctx);

    // Restore remaining goals after any new goals from tactic
    ctx.state.goals.extend(rest);

    result
}

/// Rotate goals by `n` positions.
///
/// Positive `n` rotates forward (front goals move to back).
/// Negative `n` rotates backward (back goals move to front).
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty (for non-zero `n`)
/// ENSURES: on `Ok`, `ctx.state.goals.len()` is unchanged
/// ENSURES: goals are cyclically permuted by `n` positions
pub fn eval_rotate(n: isize, ctx: &mut TacticCtx<'_>) -> TacticResult {
    if ctx.state.goals.is_empty() {
        return if n == 0 {
            Ok(())
        } else {
            Err(TacticError::NoGoals)
        };
    }

    let len = ctx.state.goals.len();
    // Normalize n into [0, len) forward rotations
    let effective = ((n % len as isize) + len as isize) as usize % len;

    if effective == 0 {
        return Ok(());
    }

    ctx.state.invalidate_tc_cache();
    // Rotate forward by `effective`: move the first `effective` goals to the back
    for _ in 0..effective {
        let goal = ctx.state.goals.pop_front().expect("goals non-empty");
        ctx.state.goals.push_back(goal);
    }

    Ok(())
}

/// Swap the first two goals.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals.len() >= 2`
/// ENSURES: on `Ok`, goals[0] and goals[1] are exchanged
/// ENSURES: on `Err(InvalidTarget)`, fewer than 2 goals; state unchanged
pub fn eval_swap(ctx: &mut TacticCtx<'_>) -> TacticResult {
    if ctx.state.goals.len() < 2 {
        return Err(TacticError::InvalidTarget {
            tactic: "swap".into(),
            detail: "need at least 2 goals".into(),
        });
    }

    ctx.state.invalidate_tc_cache();
    ctx.state.goals.swap(0, 1);
    Ok(())
}
