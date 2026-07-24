// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refine tactic and placeholder handling.
//!
//! Contains `refine`, `refine_placeholder`, `count_placeholders`, and the
//! placeholder substitution machinery including ZFC and Cubical extensions.

use crate::stack_safe;
use clean_kernel::{Expr, ExprKind};

use super::super::core::{Goal, ProofState, TacticError, TacticResult};
use super::super::proof_term::exact;
#[cfg(test)]
pub(crate) use super::refine_bridge::refine_elaborated;
use super::refine_bridge::{elaborate_placeholder_term, finish_refine, is_placeholder_name};

// ============================================================================
// refine - Term refinement with holes
// ============================================================================

/// Refine the goal with a term containing holes.
///
/// `refine` allows you to provide a partial proof term where some parts are
/// indicated as underscores/placeholders. Each hole becomes a new goal.
///
/// # Algorithm
/// 1. Parse the expression looking for placeholder expressions
/// 2. Create new metavariables for each hole
/// 3. Create new goals for each metavariable
///
/// # Example
/// ```text
/// -- Goal: P ∧ Q
/// refine ⟨?_, ?_⟩
/// -- Goal 1: P
/// -- Goal 2: Q
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `TypeMismatch` if the refined term doesn't match the goal type
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: If `term` has no placeholders, behavior matches `exact(state, term)`
/// ENSURES: On Ok with placeholders, each placeholder becomes a fresh goal in left-to-right order
/// ENSURES: On Ok with placeholders, the original goal is closed by the substituted term
pub fn refine(state: &mut ProofState, term: Expr) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    if count_placeholders(&term) == 0 {
        return exact(state, term);
    }

    let mut new_goals = Vec::new();
    let (refined_term, _) =
        elaborate_placeholder_term(state, &goal, &term, Some(&goal.target), &mut new_goals)?;
    finish_refine(state, &goal, refined_term, new_goals)
}

/// Count placeholder expressions in an expression tree
///
/// REQUIRES: `expr` is a well-formed expression tree
/// ENSURES: Returns the number of placeholder constants (`_`, `?`, `?_...`) in supported nodes
pub(crate) fn count_placeholders(expr: &Expr) -> usize {
    stack_safe(|| match expr.kind() {
        // We use a convention where a const named "_" or "?" is a placeholder
        ExprKind::Const(name, _) => usize::from(is_placeholder_name(&name.to_string())),
        ExprKind::App(f, arg) => count_placeholders(f) + count_placeholders(arg),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_placeholders(ty) + count_placeholders(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_placeholders(ty) + count_placeholders(val) + count_placeholders(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            count_placeholders(inner)
        }
        // ZFC mode extensions
        ExprKind::ZFCMem { element, set } => count_placeholders(element) + count_placeholders(set),
        ExprKind::ZFCComprehension { domain, pred } => {
            count_placeholders(domain) + count_placeholders(pred)
        }
        ExprKind::ZFCSet(set_expr) => count_placeholders_zfc(set_expr),
        // Cubical mode extensions
        ExprKind::CubicalPath { ty, left, right } => {
            count_placeholders(ty) + count_placeholders(left) + count_placeholders(right)
        }
        ExprKind::CubicalPathLam { body } => count_placeholders(body),
        ExprKind::CubicalPathApp { path, arg } => {
            count_placeholders(path) + count_placeholders(arg)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            count_placeholders(ty)
                + count_placeholders(phi)
                + count_placeholders(u)
                + count_placeholders(base)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            count_placeholders(ty) + count_placeholders(phi) + count_placeholders(base)
        }
        _ => 0,
    })
}

/// Count placeholders in ZFCSetExpr sub-expressions.
///
/// ENSURES: Returns the number of placeholder constants reachable within `set_expr`
fn count_placeholders_zfc(set_expr: &clean_kernel::expr::ZFCSetExpr) -> usize {
    use clean_kernel::expr::ZFCSetExpr;
    match set_expr {
        ZFCSetExpr::Empty => 0,
        ZFCSetExpr::Singleton(e)
        | ZFCSetExpr::Union(e)
        | ZFCSetExpr::PowerSet(e)
        | ZFCSetExpr::Choice(e) => count_placeholders(e),
        ZFCSetExpr::Pair(a, b) => count_placeholders(a) + count_placeholders(b),
        ZFCSetExpr::Separation { set, pred } => count_placeholders(set) + count_placeholders(pred),
        ZFCSetExpr::Replacement { set, func } => count_placeholders(set) + count_placeholders(func),
        ZFCSetExpr::Infinity => 0,
    }
}

/// Refine with a placeholder expression indicating a hole
/// This creates a goal with an unknown type (placeholder)
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Appends one fresh goal whose target/context match the current goal
/// ENSURES: Leaves the original current goal open
pub fn refine_placeholder(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Simply create a new metavariable goal that inherits the current target
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let placeholder = goal.target.clone();

    let new_meta_id = state.fresh_meta(placeholder.clone());
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: placeholder,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    state.goals.push_back(new_goal);
    Ok(())
}
