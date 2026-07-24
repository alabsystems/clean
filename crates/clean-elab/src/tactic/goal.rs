// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal management tactics
//!
//! Provides tactics for manipulating the goal list: swapping, rotating,
//! and selecting specific goals to focus on.

use super::{ProofState, TacticError, TacticResult};

/// Swap the first two goals in the goal list.
///
/// This is useful when you want to work on the second goal before the first.
///
/// # Example
/// ```text
/// -- Goals: [⊢ A, ⊢ B, ⊢ C]
/// swap
/// -- Goals: [⊢ B, ⊢ A, ⊢ C]
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals.len() >= 2`
/// ENSURES: On Ok, `state.goals[0]` and `state.goals[1]` are exchanged; other goals unchanged
/// ENSURES: On Err(InvalidTarget), fewer than 2 goals; state unchanged
pub fn swap(state: &mut ProofState) -> TacticResult {
    if state.goals.len() < 2 {
        return Err(TacticError::InvalidTarget {
            tactic: "swap".into(),
            detail: "need at least 2 goals".into(),
        });
    }
    state.invalidate_tc_cache();
    state.goals.swap(0, 1);
    Ok(())
}

/// Rotate goals by moving the first goal to the end.
///
/// # Example
/// ```text
/// -- Goals: [⊢ A, ⊢ B, ⊢ C]
/// rotate
/// -- Goals: [⊢ B, ⊢ C, ⊢ A]
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the former front goal is now at the back; order of others preserved
/// ENSURES: On Ok, `state.goals.len()` is unchanged
/// ENSURES: On Err(NoGoals), `state.goals` was empty; state unchanged
pub fn rotate(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    if state.goals.len() > 1 {
        let first = state.pop_current_goal()?;
        state.goals.push_back(first);
    }
    Ok(())
}

/// Rotate goals backward by moving the last goal to the front.
///
/// # Example
/// ```text
/// -- Goals: [⊢ A, ⊢ B, ⊢ C]
/// rotate_back
/// -- Goals: [⊢ C, ⊢ A, ⊢ B]
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the former back goal is now at the front; order of others preserved
/// ENSURES: On Ok, `state.goals.len()` is unchanged
/// ENSURES: On Err(NoGoals), `state.goals` was empty; state unchanged
pub fn rotate_back(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    if state.goals.len() > 1 {
        state.invalidate_tc_cache();
        let last = state
            .goals
            .pop_back()
            .expect("goals has more than 1 element");
        state.goals.push_front(last);
    }
    Ok(())
}

/// Pick and focus on a specific goal by index (0-based).
///
/// Moves the specified goal to the front of the goal list.
///
/// # Example
/// ```text
/// -- Goals: [⊢ A, ⊢ B, ⊢ C]
/// pick_goal 2
/// -- Goals: [⊢ C, ⊢ A, ⊢ B]
/// ```
///
/// # Contract
///
/// REQUIRES: `index < state.goals.len()`
/// ENSURES: On Ok, `state.goals[0]` is the former `state.goals[index]`
/// ENSURES: On Ok, `state.goals.len()` is unchanged
/// ENSURES: On Err(InvalidTarget), `index` out of bounds; state unchanged
pub fn pick_goal(state: &mut ProofState, index: usize) -> TacticResult {
    if index >= state.goals.len() {
        return Err(TacticError::InvalidTarget {
            tactic: "pick_goal".into(),
            detail: format!(
                "index {index} out of bounds (have {} goals)",
                state.goals.len()
            ),
        });
    }
    if index == 0 {
        return Ok(()); // Already at front
    }
    state.invalidate_tc_cache();
    let goal = state.goals.remove(index).expect("index checked above");
    state.goals.push_front(goal);
    Ok(())
}

/// Get the number of remaining goals.
///
/// ENSURES: Returns `0` iff `state.is_complete()`
pub fn goal_count(state: &ProofState) -> usize {
    state.goals.len()
}
