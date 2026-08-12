// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Grind tactic — congruence closure + E-matching + case splitting.
//!
//! `grind` is a powerful automation tactic being adopted by Mathlib. It combines:
//! - Preprocessing via `simp` to normalize the goal and hypotheses
//! - Congruence closure (CC) to discover equalities from hypotheses
//! - E-matching to apply rewrite lemmas from the environment
//! - Case splitting on disjunctions and if-then-else expressions
//! - Recursive descent with bounded depth and split limits
//!
//! This is an MVP implementation (~400 LOC) that delegates heavily to existing
//! tactics (`simp`, `cc`, `cases`, `by_cases`, `tauto`, `assumption`).
//!
//! Reference: Lean 4 `Lean.Elab.Tactic.Grind` (45K LOC in C++).

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::cc::{cc_with_config, CCConfig};
use super::combinator::try_tactic_preserving_state;
use super::connective::contradiction;
use super::existential::by_cases;
use super::proof_term::{apply, assumption, exact, rfl};
use super::simp::{simp, SimpConfig};
use super::tauto::tauto;
use super::{
    cert_mathverse, dec_trivial, decide, match_or, omega, solve_by_elim, subst_vars, trivial, Goal,
    ProofState, TacticError, TacticResult,
};
use crate::stack_safe;
use crate::unify::MetaState;

pub use super::grind_config::GrindConfig;

const GRIND_NO_PROGRESS: &str = "grind";
const GRIND_MAX_DEPTH_EXHAUSTED: &str = "grind/max-depth";
const GRIND_SPLIT_LIMIT_EXHAUSTED: &str = "grind/split-limit";

// ============================================================================
// Main entry points
// ============================================================================

/// Grind tactic — congruence closure + E-matching + case splitting.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err(NoProgress)`, the goal could not be closed within the
///   configured depth and split limits.
pub fn grind(state: &mut ProofState) -> TacticResult {
    grind_with_config(state, GrindConfig::default())
}

/// Grind with custom configuration.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err(NoProgress)`, no solution found within resource limits.
/// ENSURES: State may be partially modified (goals reduced) even on failure.
pub fn grind_with_config(state: &mut ProofState, config: GrindConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let mut splits_remaining = config.max_splits;

    // Phase 0: Normalize — substitute known equalities (e.g., x = 5 → replace x)
    stack_safe(|| grind_normalize(state));

    if state.is_complete() {
        return Ok(());
    }

    // Phase 1: Preprocessing — simplify goal and hypotheses
    if config.use_simp {
        stack_safe(|| grind_preprocess(state, &config));
    }

    if state.is_complete() {
        return Ok(());
    }

    // Phase 2: Core grind loop — CC + E-matching + case splitting
    stack_safe(|| grind_core(state, &config, 0, &mut splits_remaining))
}

// ============================================================================
// Preprocessing
// ============================================================================

/// Run simp to normalize the goal. Non-fatal — swallows errors.
fn grind_preprocess(state: &mut ProofState, config: &GrindConfig) {
    let simp_config = SimpConfig {
        max_steps: config.simp_max_steps,
        beta: true,
        eta: true,
        ..SimpConfig::new()
    };

    // Try simp; if it fails, that is fine — we proceed with the unnormalized goal.
    let _ = simp(state, simp_config);
}

/// Normalize hypothesis equalities by substituting known variable equalities.
///
/// If the local context contains `h : x = 5`, replaces `x` throughout the goal.
/// Non-fatal — swallows errors since normalization is opportunistic.
fn grind_normalize(state: &mut ProofState) {
    let _ = subst_vars(state);
}

// ============================================================================
// Core algorithm
// ============================================================================

/// Recursive core of grind: try closers, then CC, then case-split and recurse.
///
/// REQUIRES: `state.goals` is non-empty (caller checks).
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err`, the goal remains open (state may be partially modified).
fn grind_core(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
) -> TacticResult {
    if state.is_complete() {
        return Ok(());
    }

    if grind_max_depth_exceeded(depth, config) {
        return Err(grind_no_progress(GRIND_MAX_DEPTH_EXHAUSTED));
    }

    // Step 1: Try immediate closers (stack_safe: closers may call whnf/is_def_eq)
    if stack_safe(|| try_closers(state, config)) {
        return Ok(());
    }

    // Step 2: Congruence closure (stack_safe: CC may trigger deep type checker calls)
    if config.use_cc && stack_safe(|| try_cc(state, config)) {
        return Ok(());
    }

    // Step 3: Automation engine (SMT + superposition via clean-auto)
    if config.use_automation && stack_safe(|| try_automation_engine(state, config)) {
        return Ok(());
    }

    // Step 4: Case splitting — find a disjunction or ite to split on
    if *splits_remaining == 0 {
        return Err(grind_no_progress(GRIND_SPLIT_LIMIT_EXHAUSTED));
    }

    // Try splitting on disjunctions in hypotheses
    if config.split_disjunctions {
        if let Some(result) = try_split_disjunction(state, config, depth, splits_remaining) {
            return result;
        }
    }

    // Try splitting on ite/dite conditions in the goal
    if config.split_ite {
        if let Some(result) = try_split_ite(state, config, depth, splits_remaining) {
            return result;
        }
    }

    Err(grind_no_progress(GRIND_NO_PROGRESS))
}

fn grind_max_depth_exceeded(depth: usize, config: &GrindConfig) -> bool {
    depth > config.max_depth
}

fn grind_no_progress(tactic: &'static str) -> TacticError {
    TacticError::NoProgress {
        tactic: tactic.into(),
    }
}

// ============================================================================
// Closers
// ============================================================================

/// Try lightweight tactics to close the goal immediately.
/// Returns `true` if the goal was closed.
fn try_closers(state: &mut ProofState, config: &GrindConfig) -> bool {
    // Reflexivity
    if try_tactic_preserving_state(state, rfl) {
        return true;
    }

    // Assumption
    if try_tactic_preserving_state(state, assumption) {
        return true;
    }

    // Trivial (True, empty goals)
    if try_tactic_preserving_state(state, trivial) {
        return true;
    }

    // Contradiction
    if try_tactic_preserving_state(state, contradiction) {
        return true;
    }

    // Solve by elim with bounded depth
    let sbe_depth = config.solve_by_elim_depth;
    if try_triggered_solve_by_elim(state, sbe_depth) {
        return true;
    }
    if try_tactic_preserving_state(state, |s| solve_by_elim(s, sbe_depth)) {
        return true;
    }

    // Tauto for propositional reasoning
    if config.use_tauto && try_tactic_preserving_state(state, tauto) {
        return true;
    }

    // Arithmetic closers: project normalization, raw mathverse, decide, dec_trivial.
    if config.use_arithmetic_closers && try_arithmetic_closers(state) {
        return true;
    }

    false
}

fn try_arithmetic_closers(state: &mut ProofState) -> bool {
    if try_tactic_preserving_state(state, cert_mathverse) {
        return true;
    }
    if try_tactic_preserving_state(state, omega) {
        return true;
    }
    if try_tactic_preserving_state(state, decide) {
        return true;
    }
    if try_tactic_preserving_state(state, dec_trivial) {
        return true;
    }
    false
}

fn try_triggered_solve_by_elim(state: &mut ProofState, max_depth: usize) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let candidates = collect_ematch_trigger_candidates(&goal, &state.metas);

    for candidate in candidates {
        let Some(fvar) = goal
            .local_ctx
            .iter()
            .find(|decl| decl.name == candidate)
            .map(|decl| decl.fvar)
        else {
            continue;
        };

        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        if apply(state, Expr::fvar(fvar)).is_ok() && solve_by_elim(state, max_depth).is_ok() {
            state.metas_mut().commit();
            return true;
        }

        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
    }

    false
}

fn collect_ematch_trigger_candidates(goal: &Goal, metas: &MetaState) -> Vec<String> {
    let Some(target_head) = trigger_head(&metas.instantiate(&goal.target)) else {
        return vec![];
    };

    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let conclusion = pi_conclusion(metas.instantiate(&decl.ty));
            let conclusion_head = trigger_head(&conclusion)?;
            (conclusion_head == target_head).then(|| decl.name.clone())
        })
        .collect()
}

fn pi_conclusion(mut ty: Expr) -> Expr {
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        ty = body.as_ref().clone();
    }
    ty
}

fn trigger_head(expr: &Expr) -> Option<Expr> {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(_, _) | ExprKind::FVar(_) => Some(head.clone()),
        _ => None,
    }
}

/// Try congruence closure to close an equality goal.
/// Returns `true` if the goal was closed.
fn try_cc(state: &mut ProofState, config: &GrindConfig) -> bool {
    let cc_config = CCConfig {
        max_iterations: config.cc_max_iterations,
        verbose: false,
    };
    try_tactic_preserving_state(state, |s| cc_with_config(s, cc_config.clone()))
}

// ============================================================================
// Automation engine (SMT + superposition via clean-auto)
// ============================================================================

/// Try the clean-auto automation engine to close the goal via SMT or superposition.
///
/// The engine collects hypotheses from the local context, translates the goal to
/// an SMT query, and attempts proof reconstruction. This covers goals that require
/// combinations of equality reasoning, propositional logic, and arithmetic that
/// the simpler closers miss.
///
/// REQUIRES: `state` has at least one open goal.
/// ENSURES: Returns `true` if the goal was closed; `false` otherwise.
/// ENSURES: On `false`, state is fully restored.
fn try_automation_engine(state: &mut ProofState, config: &GrindConfig) -> bool {
    let timeout = Duration::from_millis(config.automation_timeout_ms);

    try_tactic_preserving_state(state, |s| {
        let goal = s.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let local_ctx = s.build_local_ctx(&goal);
        let target = s.metas.instantiate(&goal.target);

        let engine = AutomationEngine::new();
        let proof_result = engine
            .auto_prove(s.env(), &target, timeout, Some(&local_ctx))
            .ok_or_else(|| TacticError::NoProgress {
                tactic: "grind/automation".into(),
            })?;

        exact(s, proof_result.proof_term().clone())
    })
}

// ============================================================================
// Case splitting — disjunctions
// ============================================================================

/// Scan hypotheses for an `Or` disjunction and case-split on it.
///
/// Returns `Some(Ok(()))` if case-splitting succeeded and both branches closed,
/// `Some(Err(...))` if splitting was attempted but a branch failed,
/// `None` if no splittable disjunction was found.
fn try_split_disjunction(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
) -> Option<TacticResult> {
    let goal = state.current_goal()?.clone();

    let candidates = collect_or_hypothesis_names(&goal, &state.metas);
    if candidates.is_empty() {
        return None;
    }

    let mut last_error = None;
    for hyp_name in candidates {
        let saved_goals = state.goals.clone();
        let saved_splits_remaining = *splits_remaining;
        state.metas_mut().push_scope();

        if super::proof_manipulation::cases(state, &hyp_name).is_err() {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            *splits_remaining = saved_splits_remaining;
            state.metas_mut().pop_scope();
            continue;
        }

        *splits_remaining = splits_remaining.saturating_sub(1);
        let result = close_all_goals_recursive(state, config, depth + 1, splits_remaining);

        match result {
            Ok(()) => {
                state.metas_mut().commit();
                return Some(Ok(()));
            }
            Err(e) => {
                state.invalidate_tc_cache();
                state.goals = saved_goals;
                *splits_remaining = saved_splits_remaining;
                state.metas_mut().pop_scope();
                last_error = Some(e);
            }
        }
    }

    last_error.map(Err)
}

fn collect_or_hypothesis_names(goal: &Goal, metas: &MetaState) -> Vec<String> {
    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let ty = metas.instantiate(&decl.ty);
            match_or(&ty).map(|_| decl.name.clone())
        })
        .collect()
}

// ============================================================================
// Case splitting — if-then-else
// ============================================================================

/// Scan the goal target for an `ite` condition and split on it via `by_cases`.
///
/// Returns `Some(Ok(()))` if case-splitting succeeded and both branches closed,
/// `Some(Err(...))` if splitting was attempted but a branch failed,
/// `None` if no ite condition was found.
fn try_split_ite(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
) -> Option<TacticResult> {
    let goal = state.current_goal()?.clone();
    let target = state.metas.instantiate(&goal.target);
    let condition = find_ite_condition(&target)?;

    // Save state for rollback
    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();

    // by_cases on the ite condition
    let case_name = format!("h_grind_{depth}");
    if by_cases(state, &case_name, condition).is_err() {
        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
        return None;
    }

    *splits_remaining = splits_remaining.saturating_sub(1);

    // Try to close both branches
    let result = close_all_goals_recursive(state, config, depth + 1, splits_remaining);

    match result {
        Ok(()) => {
            state.metas_mut().commit();
            Some(Ok(()))
        }
        Err(e) => {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
            Some(Err(e))
        }
    }
}

/// Extract the condition `P` from the first `@ite P _ _ _` or `@dite P _ _ _`
/// found in the expression.
fn find_ite_condition(expr: &Expr) -> Option<Expr> {
    stack_safe(|| find_ite_condition_inner(expr))
}

fn find_ite_condition_inner(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::App(f, _) => {
            // ite is `@ite P inst t e` = App(App(App(App(Const "ite", _), P), inst), t), e)
            // dite is `@dite P inst t e`
            // We need to find the head and check if it's ite/dite with enough args.
            let head = expr.get_app_fn();
            let args: Vec<&Expr> = expr.get_app_args().into_iter().collect();

            if let ExprKind::Const(name, _) = head.kind() {
                let name_str = name.to_string();
                if (name_str == "ite" || name_str == "dite") && args.len() >= 4 {
                    return Some(args[0].clone());
                }
            }

            // Recurse into subexpressions
            find_ite_condition_inner(f).or_else(|| {
                if let ExprKind::App(_, a) = expr.kind() {
                    find_ite_condition_inner(a)
                } else {
                    None
                }
            })
        }
        ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
            find_ite_condition_inner(dom).or_else(|| find_ite_condition_inner(body))
        }
        _ => None,
    }
}

// ============================================================================
// Recursive goal closing
// ============================================================================

/// Attempt to close all current goals by running the grind core on each.
///
/// REQUIRES: `state` has one or more goals.
/// ENSURES: On `Ok(())`, all goals are closed.
/// ENSURES: On `Err`, at least one goal could not be closed.
fn close_all_goals_recursive(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
) -> TacticResult {
    // Process each goal in sequence. After closing goal 0, goal 1 becomes goal 0.
    let max_goals = state.goals.len();
    for _ in 0..max_goals {
        if state.is_complete() {
            return Ok(());
        }

        // Preprocess this branch
        if config.use_simp {
            grind_preprocess(state, config);
        }

        if state.is_complete() {
            return Ok(());
        }

        // Recurse
        grind_core(state, config, depth, splits_remaining)?;
    }

    if state.is_complete() {
        Ok(())
    } else {
        Err(grind_no_progress(GRIND_NO_PROGRESS))
    }
}

// ============================================================================
// E-matching helpers
// ============================================================================

/// Collect rewrite-eligible equality hypotheses from the local context.
///
/// Returns pairs `(lhs, rhs)` from hypotheses of the form `lhs = rhs`.
/// Used by CC and the automation engine E-matching passes.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn collect_eq_hypotheses(goal: &Goal, metas: &MetaState) -> Vec<(Expr, Expr)> {
    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let ty = metas.instantiate(&decl.ty);
            super::match_eq_simple(&ty)
        })
        .collect()
}

#[cfg(test)]
#[path = "grind_tests.rs"]
mod grind_tests;
