// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured case analysis with pattern matching.
//!
//! Provides `eval_cases` for basic case splitting and `eval_rcases` for
//! recursive case analysis with user-supplied naming patterns. The existing
//! `cases` tactic in `proof_manipulation.rs` performs the core case split;
//! this module adds pattern-directed naming and recursive destruction.
//!
//! # Pattern Language
//!
//! `RCasesPattern` describes how constructor fields should be named and
//! recursively destructed:
//!
//! - `Name(s)` — bind the field to `s`
//! - `Tuple(pats)` — recursively destruct the field and apply `pats` to its sub-fields
//! - `Wildcard` — accept the auto-generated name without further destruction

use crate::stack_safe;
use clean_kernel::ExprKind;

use super::core::{Goal, ProofState, TacticResult};
use super::proof_manipulation::cases;

/// Pattern for naming/destructing fields in `rcases`.
///
/// Mirrors Lean 4's `rcases` pattern syntax. Each constructor field can be
/// given a name, destructed recursively via a tuple pattern, or left unnamed
/// with a wildcard.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RCasesPattern {
    /// Bind the field to a user-supplied name.
    Name(String),
    /// Recursively destruct the field using nested patterns.
    Tuple(Vec<RCasesPattern>),
    /// Accept the auto-generated name; do not destruct further.
    Wildcard,
}

/// Perform structural case analysis on `target`, applying `patterns` to name
/// the resulting constructor fields.
///
/// This is the entry point for `rcases target with ⟨p1, p2, ...⟩`. Each
/// top-level pattern corresponds to a constructor of the target's inductive
/// type. If fewer patterns than constructors are supplied, the remaining
/// constructors use wildcard naming. If a `Tuple` pattern is supplied for
/// a field, that field is recursively destructed.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `target` refers to a hypothesis whose type is an inductive type.
/// ENSURES: On Ok, the current goal is replaced by one goal per constructor.
/// ENSURES: Constructor fields are renamed according to `patterns`.
/// ENSURES: `Tuple` sub-patterns trigger recursive case analysis on the field.
/// ENSURES: On Err, the proof state may be partially modified (consistent with `cases`).
pub fn eval_rcases(
    state: &mut ProofState,
    target: &str,
    patterns: &[RCasesPattern],
) -> TacticResult {
    stack_safe(|| eval_rcases_inner(state, target, patterns))
}

/// Inner implementation of pattern-directed rcases (stack-safe wrapper above).
fn eval_rcases_inner(
    state: &mut ProofState,
    target: &str,
    patterns: &[RCasesPattern],
) -> TacticResult {
    // Count goals before the case split to identify newly created goals.
    let goals_before = state.goals.len();

    // Perform the base case split.
    cases(state, target)?;

    let goals_after = state.goals.len();
    // `cases` removes the current goal and pushes new ones at the back.
    // The new goals occupy indices [goals_before - 1 .. goals_after - 1].
    // (One goal was consumed, so net new = goals_after - goals_before + 1.)
    let num_new = goals_after.saturating_sub(goals_before) + 1;
    let new_goal_start = goals_after.saturating_sub(num_new);

    // Apply patterns to the new goals (one pattern per constructor).
    for (ctor_idx, goal_idx) in (new_goal_start..goals_after).enumerate() {
        if goal_idx >= state.goals.len() {
            break;
        }

        let pattern = patterns.get(ctor_idx).unwrap_or(&RCasesPattern::Wildcard);

        match pattern {
            RCasesPattern::Wildcard => {
                // Nothing to do — keep auto-generated names.
            }
            RCasesPattern::Name(name) => {
                // Single-name pattern: rename the first field hypothesis.
                // The constructor tag tells us the field name prefix.
                let goal = &state.goals[goal_idx];
                if let Some(first_field_idx) = find_first_field_idx(goal) {
                    state.goals[goal_idx].local_ctx[first_field_idx].name = name.clone();
                }
            }
            RCasesPattern::Tuple(sub_patterns) => {
                // Apply sub-patterns to the fields of this constructor.
                apply_field_patterns(state, goal_idx, sub_patterns)?;
            }
        }
    }

    Ok(())
}

/// Perform basic case analysis (thin wrapper over `proof_manipulation::cases`).
///
/// This is identical to the core `cases` tactic but provided here for
/// consistent naming alongside `eval_rcases`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `target` refers to a hypothesis whose type is an inductive type.
/// ENSURES: On Ok, the current goal is replaced by one goal per constructor.
pub fn eval_cases(state: &mut ProofState, target: &str) -> TacticResult {
    cases(state, target)
}

/// Find the index of the first constructor field in the goal's local context.
///
/// Constructor fields are added at the end of the local context by `cases`.
/// We identify them by looking for names matching the goal's tag (constructor
/// short name) prefix pattern `{tag}_N`.
fn find_first_field_idx(goal: &Goal) -> Option<usize> {
    let tag = goal.tag.as_deref()?;
    let prefix = format!("{tag}_");
    goal.local_ctx
        .iter()
        .position(|d| d.name.starts_with(&prefix))
}

/// Apply sub-patterns to the fields of a constructor goal at `goal_idx`.
///
/// Each sub-pattern in `patterns` is applied positionally to the constructor
/// fields (identified by the `{tag}_N` naming convention). `Name` patterns
/// rename, `Tuple` patterns trigger recursive destruction, and `Wildcard`
/// patterns leave the auto-generated name.
///
/// REQUIRES: `goal_idx` is a valid index into `state.goals`.
/// ENSURES: Field hypotheses are renamed according to `patterns`.
/// ENSURES: `Tuple` sub-patterns trigger recursive case analysis on those fields.
fn apply_field_patterns(
    state: &mut ProofState,
    goal_idx: usize,
    patterns: &[RCasesPattern],
) -> TacticResult {
    let goal = &state.goals[goal_idx];
    let tag = goal.tag.as_deref().unwrap_or("").to_string();
    let prefix = format!("{tag}_");

    // Collect field indices and names.
    let field_entries: Vec<(usize, String)> = goal
        .local_ctx
        .iter()
        .enumerate()
        .filter(|(_, d)| d.name.starts_with(&prefix))
        .map(|(i, d)| (i, d.name.clone()))
        .collect();

    // Track fields that need recursive destruction after renaming.
    let mut recursive_targets: Vec<(String, Vec<RCasesPattern>)> = Vec::new();

    for (pat_idx, pat) in patterns.iter().enumerate() {
        if pat_idx >= field_entries.len() {
            break;
        }
        let (ctx_idx, _old_name) = &field_entries[pat_idx];

        match pat {
            RCasesPattern::Wildcard => {}
            RCasesPattern::Name(new_name) => {
                state.goals[goal_idx].local_ctx[*ctx_idx].name = new_name.clone();
            }
            RCasesPattern::Tuple(sub_pats) => {
                // Give the field a temporary name, then plan recursive destruction.
                let temp_name = format!("_rcases_{pat_idx}");
                let final_name = state.goals[goal_idx].local_ctx[*ctx_idx].name.clone();
                state.goals[goal_idx].local_ctx[*ctx_idx].name = temp_name.clone();
                // Check if the field type is an inductive type before planning recursion.
                let field_ty = state.goals[goal_idx].local_ctx[*ctx_idx].ty.clone();
                let goal_ref = &state.goals[goal_idx];
                let field_ty_whnf = state.whnf(goal_ref, &field_ty);
                let head = field_ty_whnf.get_app_fn();
                if let ExprKind::Const(name, _) = head.kind() {
                    if state.env.get_inductive(name).is_some() {
                        recursive_targets.push((temp_name, sub_pats.clone()));
                        continue;
                    }
                }
                // Not inductive — just rename with the first sub-pattern name or keep.
                if let Some(RCasesPattern::Name(n)) = sub_pats.first() {
                    state.goals[goal_idx].local_ctx[*ctx_idx].name = n.clone();
                } else {
                    state.goals[goal_idx].local_ctx[*ctx_idx].name = final_name;
                }
            }
        }
    }

    // Perform recursive destructions. Each recursion may change goal structure,
    // so we re-focus on the goal after each step.
    for (target_name, sub_pats) in recursive_targets {
        // Focus on the goal at goal_idx by moving it to front.
        if goal_idx > 0 && goal_idx < state.goals.len() {
            let g = state.goals.remove(goal_idx).expect("valid index");
            state.goals.push_front(g);
        }
        // Snapshot for rollback.
        let goals_snapshot = state.goals.clone();
        state.metas.push_scope();
        let next_fvar_snapshot = state.next_fvar;

        match eval_rcases_inner(state, &target_name, &sub_pats) {
            Ok(()) => {
                state.metas.commit();
            }
            Err(_) => {
                // Restore on failure — the field is not recursively destructible.
                state.metas.pop_scope();
                state.goals = goals_snapshot;
                state.next_fvar = next_fvar_snapshot;
                state.invalidate_tc_cache();
            }
        }
    }

    Ok(())
}

/// Recursive cases with depth limit (no patterns).
///
/// Convenience wrapper: destructs nested inductive types up to `max_depth`
/// levels without user-supplied naming. Delegates to the existing `rcases`
/// in `inductive_reasoning.rs`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `target` refers to a hypothesis whose type is an inductive type.
/// ENSURES: Nested inductive types are destructed recursively up to `max_depth`.
pub fn eval_rcases_depth(state: &mut ProofState, target: &str, max_depth: usize) -> TacticResult {
    super::inductive_reasoning::rcases(state, target, max_depth)
}
