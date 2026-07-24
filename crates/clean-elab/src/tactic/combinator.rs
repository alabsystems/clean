// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic combinators for composing and controlling tactic execution.
//!
//! Provides combinators for trying, repeating, sequencing, and focusing tactics:
//! - `try_tactic` — run a tactic but succeed even if it fails
//! - `repeat_tactic` — apply a tactic repeatedly until failure
//! - `first_tactic` — try tactics in order until one succeeds
//! - `all_goals` / `any_goals` — apply to all goals
//! - `focus` — apply to only the first goal
//! - `trivial` — try basic closers (assumption, rfl)

use super::core::{ProofState, TacticError, TacticResult};
use super::proof_term::{assumption, constructor, rfl};

/// A tactic is a function that transforms a proof state.
pub type Tactic = Box<dyn FnOnce(&mut ProofState) -> TacticResult>;

/// The `try_tactic` combinator runs a tactic but succeeds even if it fails.
///
/// This is useful for tactics that may not always apply but shouldn't
/// cause the overall proof script to fail.
///
/// REQUIRES: `state` has a valid meta scope stack (push_scope/pop_scope balanced)
///
/// ENSURES: always returns Ok(()) — on tactic success the state is advanced,
/// on tactic failure the state is fully restored to pre-call
///
/// # Example
/// ```text
/// try_tactic(|| rfl(state))  -- succeeds even if rfl fails
/// ```
pub fn try_tactic<F>(state: &mut ProofState, tactic: F) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    // Save goals and push scope for metas in case tactic fails
    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();

    if tactic(state).is_ok() {
        // Commit scope - tactic succeeded
        state.metas_mut().commit();
        Ok(())
    } else {
        // Restore state and succeed anyway
        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
        Ok(())
    }
}

/// The `repeat_tactic` combinator runs a tactic repeatedly until it fails.
///
/// Returns success after applying the tactic zero or more times.
/// The state after the last successful application is kept.
///
/// REQUIRES: `max_iterations > 0` for the tactic to be attempted at all
///
/// ENSURES: always returns Ok(()) — state reflects the last successful
/// application; meta scope stack remains balanced regardless of how many
/// iterations succeeded or failed
///
/// # Example
/// ```text
/// repeat_tactic(|| intro(state, "h"))  -- introduces all hypotheses
/// ```
///
/// # Arguments
/// * `max_iterations` - Maximum number of iterations (prevents infinite loops)
pub fn repeat_tactic<F>(
    state: &mut ProofState,
    mut tactic_factory: F,
    max_iterations: usize,
) -> TacticResult
where
    F: FnMut() -> Box<dyn FnOnce(&mut ProofState) -> TacticResult>,
{
    for _ in 0..max_iterations {
        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        let tactic = tactic_factory();
        if tactic(state).is_ok() {
            // Tactic succeeded, commit and continue
            state.metas_mut().commit();
            if state.is_complete() {
                break; // No more goals to work on
            }
        } else {
            // Tactic failed, restore and stop
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
            break;
        }
    }
    Ok(())
}

/// The `first_tactic` combinator tries tactics in order until one succeeds.
///
/// Returns success if any tactic succeeds.
///
/// Earlier branches backtrack only on recoverable tactic failures. The final
/// branch runs directly so its specific error is preserved.
///
/// REQUIRES: `tactics` is non-empty (empty list always returns AllTacticsFailed)
///
/// ENSURES: on Ok, exactly one tactic succeeded and its state is committed;
/// on Err, earlier backtracked branches are restored before propagating the
/// failing error
///
/// # Example
/// ```text
/// first_tactic(vec![
///     || assumption(state),
///     || rfl(state),
///     || trivial(state),
/// ])
/// ```
pub fn first_tactic<F>(state: &mut ProofState, tactics: Vec<F>) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let saved_goals = state.goals.clone();
    let tactic_count = tactics.len();

    for (idx, tactic) in tactics.into_iter().enumerate() {
        if idx + 1 == tactic_count {
            return tactic(state);
        }

        state.metas_mut().push_scope();
        match tactic(state) {
            Ok(()) => {
                state.metas_mut().commit();
                return Ok(());
            }
            Err(err) => {
                state.invalidate_tc_cache();
                state.goals = saved_goals.clone();
                state.metas_mut().pop_scope();
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

/// The `all_goals` combinator applies a tactic to all goals.
///
/// The tactic is applied to each goal in order. If any application fails,
/// the entire combinator fails.
///
/// REQUIRES: `state.goals` is non-empty (NoGoals semantics delegated to inner tactic)
///
/// ENSURES: on Ok, tactic was applied to every original goal (new goals
/// from sub-tactics are not re-processed); on Err, partial progress from
/// earlier goals may remain
///
/// # Example
/// ```text
/// all_goals(|| assumption(state))  -- try assumption on all goals
/// ```
pub fn all_goals<F>(state: &mut ProofState, mut tactic_factory: F) -> TacticResult
where
    F: FnMut() -> Box<dyn FnOnce(&mut ProofState) -> TacticResult>,
{
    // Apply tactic to each goal
    // We need to be careful: applying a tactic may create new goals
    // We want to apply to the original goals, not new ones
    let original_goal_count = state.goals.len();
    let mut processed = 0;

    while processed < original_goal_count && !state.goals.is_empty() {
        let tactic = tactic_factory();
        tactic(state)?;
        processed += 1;
    }

    Ok(())
}

/// The `any_goals` combinator applies a tactic to all goals, succeeding if any succeed.
///
/// Unlike `all_goals`, this continues even if some goals fail and only
/// returns error if ALL goals fail.
///
/// REQUIRES: `state.goals` is non-empty
///
/// ENSURES: on Ok, at least one original goal succeeded and its state
/// is committed; failed goals are rotated to the back unchanged;
/// on Err(AllTacticsFailed), all goals are restored to pre-call positions
///
/// # Example
/// ```text
/// any_goals(|| assumption(state))  -- assumption on goals that have a matching hyp
/// ```
pub fn any_goals<F>(state: &mut ProofState, mut tactic_factory: F) -> TacticResult
where
    F: FnMut() -> Box<dyn FnOnce(&mut ProofState) -> TacticResult>,
{
    let original_goal_count = state.goals.len();
    let mut processed = 0;
    let mut any_succeeded = false;

    while processed < original_goal_count && !state.goals.is_empty() {
        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        let tactic = tactic_factory();
        if tactic(state).is_ok() {
            // Commit scope - tactic succeeded
            state.metas_mut().commit();
            any_succeeded = true;
        } else {
            // Restore state for this goal and skip it
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
            // Move to next goal by rotating
            if !state.goals.is_empty() {
                let goal = state.pop_current_goal()?;
                state.goals.push_back(goal);
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

/// The `focus` combinator applies a tactic to only the first goal.
///
/// This is useful when you want to work on a specific goal without
/// affecting others.
///
/// REQUIRES: `state.goals` is non-empty
///
/// ENSURES: remaining goals (index 1..) are preserved in order after
/// any new goals the tactic creates; returns the tactic's result
pub fn focus<F>(state: &mut ProofState, tactic: F) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Temporarily remove all but the first goal
    let rest = state.goals.split_off(1);

    let result = tactic(state);

    // Restore remaining goals (after any new goals from tactic)
    state.goals.extend(rest);

    result
}

/// The `focus_and_done` combinator focuses on the first goal and requires closure.
///
/// Implements Lean 4's `focusAndDone` semantics: isolate goal 0, run the tactic,
/// then check that zero unsolved goals remain in the focused scope. If any goals
/// remain after the tactic, returns `TacticError::UnsolvedGoals`.
///
/// Used by braced tactic blocks (`{ tacs }`) and cdot focus (`· tacs`).
///
/// REQUIRES: `state.goals` is non-empty
///
/// ENSURES: on Ok, the focused goal and all subgoals it generated are closed;
/// remaining goals (index 1..) are restored; on Err(UnsolvedGoals), remaining
/// goals are still restored so the proof state stays consistent
pub fn focus_and_done<F>(state: &mut ProofState, tactic: F) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Temporarily remove all but the first goal
    let rest = state.goals.split_off(1);

    let result = tactic(state);

    if result.is_err() {
        // Restore remaining goals even on failure
        state.goals.extend(rest);
        return result;
    }

    // Check that the focused goal is fully closed
    if !state.goals.is_empty() {
        let remaining = state.goals.len();
        state.goals.extend(rest);
        return Err(TacticError::UnsolvedGoals {
            count: remaining,
            detail: String::new(),
        });
    }

    // Restore the rest of the goals
    state.goals.extend(rest);
    Ok(())
}

/// Simple automation tactic that tries several basic tactics.
///
/// Tries: assumption, rfl (if available)
///
/// REQUIRES: `state.goals` is non-empty
///
/// ENSURES: on Ok, current goal is closed via assumption or rfl;
/// on Err(AllTacticsFailed), state is unchanged
pub fn trivial(state: &mut ProofState) -> TacticResult {
    // Part of #2474: wrap each branch in try_tactic_preserving_state to prevent
    // failed tactics from leaking partial state mutations to subsequent branches.
    if try_tactic_preserving_state(state, assumption) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, rfl) {
        return Ok(());
    }

    // Close a goal whose head constructor takes no arguments (e.g. `⊢ True` via
    // `True.intro`). SOUNDNESS: accept ONLY if the goal count strictly DECREASES —
    // i.e. the goal was fully discharged, not split into subgoals. Without this
    // guard `constructor` on `⊢ A ∧ B` would "succeed" while leaving `A`, `B` open,
    // violating trivial's contract that success means closed.
    let goals_before = state.goals.len();
    if try_tactic_preserving_state(state, |s| {
        constructor(s)?;
        if s.goals.len() < goals_before {
            Ok(())
        } else {
            Err(TacticError::AllTacticsFailed {
                combinator: "trivial:constructor".into(),
            })
        }
    }) {
        return Ok(());
    }

    Err(TacticError::AllTacticsFailed {
        combinator: "trivial".into(),
    })
}

/// Try a tactic and restore the proof state if it fails.
///
/// This is useful for automation tactics that want to try multiple strategies
/// without leaving partial progress behind on failure.
///
/// REQUIRES: `state` has a valid meta scope stack
///
/// ENSURES: returns true iff tactic succeeded and state is committed;
/// on false, goals and meta state are fully restored to pre-call
pub(crate) fn try_tactic_preserving_state<F>(state: &mut ProofState, tactic: F) -> bool
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();

    if tactic(state).is_ok() {
        state.metas_mut().commit();
        true
    } else {
        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
        false
    }
}
