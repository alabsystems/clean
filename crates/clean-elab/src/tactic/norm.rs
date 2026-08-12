// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Numeric normalization tactics.
//!
//! Contains `norm_num` for evaluating numeric expressions (natural numbers,
//! integers, rationals, comparisons).
//! AC-reflexivity (`ac_rfl`) is in ac_rfl.rs (#307 split).

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::combinator::try_tactic_preserving_state;
use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::nat_expr_eval;
use super::norm_num_kernel::norm_num_kernel_proof;
use super::proof_term::{reduce_eq, rfl};
// Kernel-evaluating `decide` ladder, not the bare SMT bridge — see the note in
// `norm_num.rs`. `smt::decide` refutes true ground goals; `eval_decide` proves
// them and still falls through to `smt::decide` last.
use super::decide::eval_decide as decide;

// Re-export for existing test surface (tests call `crate::tactic::norm::eval_nat_expr`)
pub(crate) use nat_expr_eval::eval_nat_expr;

/// Numeric normalization tactic.
///
/// Evaluates numeric expressions involving natural numbers, integers,
/// and rationals. Uses computation to prove equalities.
///
/// # Supported
/// - Natural number arithmetic (+, *, -, ^)
/// - Integer arithmetic
/// - Rational arithmetic
/// - Comparisons (<, ≤, >, ≥)
/// - Divisibility (∣)
/// - GCD, LCM
///
/// # Example
/// ```text
/// -- Goal: 2 + 2 = 4
/// norm_num
/// -- Goal closed
///
/// -- Goal: 3 < 5
/// norm_num
/// -- Goal closed
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if numeric evaluation fails to close the goal
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed via `decide`, `rfl`, or `reduce_eq`
/// ENSURES: On Err(ArithmeticFailed), LHS and RHS evaluate to different values
/// ENSURES: Evaluation is sound: only closes goals where both sides reduce to same value
pub fn norm_num(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = &goal.target;

    // Try to evaluate the goal
    if try_eval_prop(target) {
        // Part of #2474: wrap in try_tactic_preserving_state to prevent failed
        // decide from leaking partial state mutations before rfl runs.
        if try_tactic_preserving_state(state, decide) {
            return Ok(());
        }
        if try_tactic_preserving_state(state, rfl) {
            return Ok(());
        }
    }

    // Try the kernel proof path first (Part of #3369): constructs an
    // explicit Eq.refl proof term on the evaluated normal form rather
    // than relying on the kernel's internal def-eq check via `rfl`.
    if let Ok(proof) = norm_num_kernel_proof(target) {
        let goal_clone = goal.clone();
        if state.close_goal(&goal_clone, proof).is_ok() {
            return Ok(());
        }
    }

    // Check if goal is an equality and try to normalize both sides
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(target) {
        let lhs_val = eval_nat_expr(&lhs);
        let rhs_val = eval_nat_expr(&rhs);

        if let (Some(l), Some(r)) = (lhs_val, rhs_val) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num".into(),
                reason: format!("{l} ≠ {r}"),
            });
        }
    }

    // Check for comparisons
    if let Some(result) = try_eval_comparison(target) {
        if result {
            // True comparison - use decide
            return decide(state);
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "norm_num".to_string(),
            reason: "comparison is false".to_string(),
        });
    }

    // Fallback: reduce_eq for computational equality (#685)
    reduce_eq(state).map_err(|_| TacticError::ArithmeticFailed {
        tactic: "norm_num".to_string(),
        reason: "could not evaluate numeric goal".to_string(),
    })
}

/// Try to evaluate a proposition to true/false
fn try_eval_prop(expr: &Expr) -> bool {
    // Check for True
    if let ExprKind::Const(name, _) = expr.kind() {
        if name == &Name::from_string("True") {
            return true;
        }
    }

    // Check for comparisons
    if let Some(result) = try_eval_comparison(expr) {
        return result;
    }

    // Check for equality
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            return l == r;
        }
    }

    false
}

/// Try to evaluate a comparison expression
fn try_eval_comparison(expr: &Expr) -> Option<bool> {
    // Extract comparison: op lhs rhs
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }

    if let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() {
        let op_str = op_name.to_string();
        let l = eval_nat_expr(args[args.len() - 2])?;
        let r = eval_nat_expr(args[args.len() - 1])?;

        if op_str.contains("LT.lt") || op_str.contains("Nat.lt") {
            return Some(l < r);
        }
        if op_str.contains("LE.le") || op_str.contains("Nat.le") {
            return Some(l <= r);
        }
        if op_str.contains("GT.gt") {
            return Some(l > r);
        }
        if op_str.contains("GE.ge") {
            return Some(l >= r);
        }
    }

    None
}
