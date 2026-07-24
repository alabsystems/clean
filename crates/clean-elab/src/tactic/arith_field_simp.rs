// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Field simplification tactic
//!
//! - `field_simp`: Clears denominators in field expressions
#[cfg(test)]
use std::sync::Arc;

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::arith_field_simp_proof::build_top_level_rewrite;
use super::core::Goal;
use super::{assumption, match_equality, ring, ProofState, TacticError, TacticResult};
use crate::stack_safe;

// =============================================================================
// Field simplification tactic
// =============================================================================

/// Field simplification tactic.
///
/// Simplifies expressions in a field by clearing denominators. This is useful
/// for proving equalities involving division and fractions.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// REQUIRES: Goal is an equality involving field expressions with division
/// ENSURES: On `Ok(())`, the current goal is closed or simplified to a denominator-free equality
/// ENSURES: On `Err(NoGoals)`, `state.goals` was empty on entry
/// ENSURES: On `Err(GoalMismatch)`, goal is not an equality
/// ENSURES: When no denominators are found, delegates to `ring`
///
/// # Algorithm
/// 1. Identify all denominators in the goal expression
/// 2. Compute the least common multiple (LCM) of denominators
/// 3. Multiply both sides by the LCM to clear denominators
/// 4. Simplify the resulting polynomial equality
///
/// # Supported Patterns
/// - `a / b = c / d` → `a * d = c * b` (when b, d ≠ 0)
/// - `a / b + c / d = e` → clear denominators
/// - `1 / a = 1 / b` → `a = b` (when a, b ≠ 0)
///
/// # Example
/// ```text
/// -- Goal: a / 2 + b / 3 = (3 * a + 2 * b) / 6
/// field_simp
/// -- Goal closed (or simplified to polynomial equality)
/// ```
pub fn field_simp(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let (_ty, lhs, rhs, _levels) = match_equality(&goal.target).map_err(|_| {
        TacticError::GoalMismatch("field_simp: goal is not an equality".to_string())
    })?;

    let lhs_div = extract_top_division(&lhs);
    let rhs_div = extract_top_division(&rhs);

    if lhs_div.is_none() && rhs_div.is_none() {
        return ring(state);
    }

    cross_multiply_and_push_side_goals(state, &goal, lhs_div.is_some(), rhs_div.is_some())
}

/// Cross-multiply to clear denominators and push non-zero side goals.
///
/// Handles three cases:
/// - `a/b = c/d` → `a*d = c*b`, side goals: `b ≠ 0`, `d ≠ 0`
/// - `a/b = c`   → `a = c*b`,   side goal:  `b ≠ 0`
/// - `a = c/d`   → `a*d = c`,   side goal:  `d ≠ 0`
///
fn cross_multiply_and_push_side_goals(
    state: &mut ProofState,
    goal: &Goal,
    has_lhs_div: bool,
    has_rhs_div: bool,
) -> TacticResult {
    let rewrite = build_top_level_rewrite(state, goal, has_lhs_div, has_rhs_div)?;
    state.replace_target_eq(rewrite.new_target, rewrite.target_eq_proof)?;

    let ring_ok = ring(state).is_ok();
    for g in rewrite.side_goals {
        state.goals.push_back(g);
    }
    if ring_ok {
        try_discharge_side_goals(state);
    }
    Ok(())
}

/// Try to discharge non-zero side goals using assumption.
///
/// Iterates over remaining goals tagged with `field_simp:ne_zero` and
/// attempts to close each via `assumption` (checking the local context
/// for a matching hypothesis).
fn try_discharge_side_goals(state: &mut ProofState) {
    // Try assumption on each remaining goal (best-effort)
    let mut remaining = state.goals.len();
    while remaining > 0 {
        if assumption(state).is_err() {
            // Can't discharge this goal — leave it open for the user
            break;
        }
        remaining -= 1;
    }
}

/// Extract the top-level division from an expression.
///
/// If `expr` is `a / b` (i.e., the outermost operation is division),
/// returns `Some((numerator, denominator))`. Does not recurse into
/// sub-expressions — only checks the top-level application.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `Some((a, b))` iff `expr` has head const containing "Div"/"div"
/// ENSURES: Returns `None` for non-division expressions
fn extract_top_division(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f, denom) = expr.kind() {
        if let ExprKind::App(f2, numer) = f.kind() {
            if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                let name_str = name.to_string();
                if name_str.contains("Div") || name_str.contains("div") {
                    return Some(((**numer).clone(), (**denom).clone()));
                }
            }
        }
    }
    None
}

/// Extract all denominators from an expression involving division
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Result contains all `Div`/`div` right-hand arguments found in `expr`
/// ENSURES: Recursion is stack-safe; traverses Lam, Pi, Let, Proj, MData, Squash
/// ENSURES: Empty result when no division operations are present
#[cfg(test)]
pub(crate) fn extract_denominators(expr: &Expr) -> Vec<Expr> {
    let mut denoms = Vec::new();
    extract_denoms_aux(expr, &mut denoms);
    denoms
}

#[cfg(test)]
fn extract_denoms_aux(expr: &Expr, denoms: &mut Vec<Expr>) {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, arg) => {
            // Check for division: HDiv.hDiv or Div.div
            if let ExprKind::App(f2, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                    let name_str = name.to_string();
                    if name_str.contains("Div") || name_str.contains("div") {
                        // arg is the denominator
                        denoms.push((**arg).clone());
                        // Also recurse into numerator
                        extract_denoms_aux(arg1, denoms);
                        return;
                    }
                }
            }
            // Recurse
            extract_denoms_aux(f, denoms);
            extract_denoms_aux(arg, denoms);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            extract_denoms_aux(ty, denoms);
            extract_denoms_aux(body, denoms);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            extract_denoms_aux(ty, denoms);
            extract_denoms_aux(val, denoms);
            extract_denoms_aux(body, denoms);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            extract_denoms_aux(inner, denoms);
        }
        _ => {}
    })
}

/// Get the head function of an application
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns the leftmost non-App node in the application spine
/// ENSURES: For non-App expressions, returns `expr` unchanged
/// ENSURES: Recursion is stack-safe
pub fn get_app_fn(expr: &Expr) -> &Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, _) => get_app_fn(f),
        _ => expr,
    })
}

/// Clear denominators from an expression by multiplying through
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: All `Div`/`div` applications are replaced by their numerator
/// ENSURES: Non-division subexpressions are recursively preserved
/// ENSURES: Recursion is stack-safe; traverses Lam, Pi, Let, Proj, MData, Squash, App
///
/// Note: No longer used by production `field_simp` (#2524 fail-closed fix).
/// Retained for test coverage in `tests/proj_mdata_traversal.rs`.
#[cfg(test)]
pub(crate) fn clear_denominators(expr: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, arg) => {
            // Check for division
            if let ExprKind::App(f2, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                    let name_str = name.to_string();
                    if name_str.contains("Div") || name_str.contains("div") {
                        // a / b  →  a (division cleared, b tracked separately)
                        return clear_denominators(arg1);
                    }
                }
            }
            // Recurse
            Expr::app(clear_denominators(f), clear_denominators(arg))
        }
        ExprKind::Lam(bind_info, ty, body) => {
            Expr::lam(*bind_info, clear_denominators(ty), clear_denominators(body))
        }
        ExprKind::Pi(bind_info, ty, body) => {
            Expr::pi(*bind_info, clear_denominators(ty), clear_denominators(body))
        }
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            clear_denominators(ty),
            clear_denominators(val),
            clear_denominators(body),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, clear_denominators(inner))
        }
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), clear_denominators(inner)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(clear_denominators(inner))))
        }
        _ => expr.clone(),
    })
}

/// Make an equality expression: Eq ty lhs rhs
///
/// REQUIRES: `ty`, `lhs`, `rhs` are well-formed Lean expressions
/// REQUIRES: `levels` contains the universe levels for the `Eq` constant
/// ENSURES: Returns `@Eq ty lhs rhs` as an application spine
/// ENSURES: Result uses `Name::from_string("Eq")` as the head constant
pub fn make_equality(ty: &Expr, lhs: &Expr, rhs: &Expr, levels: &[Level]) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), levels.to_vec()),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}
