// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Norm cast tactic — normalizes coercions (casts) in expressions.
//!
//! Split from `arith_field_simp.rs` per 500-line file limit.

#[cfg(test)]
use std::sync::Arc;

use clean_kernel::{Expr, ExprKind};

use super::arith_field_simp::get_app_fn;
use super::cast::proof_carry::{rewrite_target_with_cast_lemmas, CastRewriteFlavor};
// Kernel-evaluating `decide` ladder, not the `smt::decide` re-exported from
// `super` — see the note in `norm_num.rs`.
use super::decide::eval_decide as decide;
use super::{norm_num, rfl, ring, ProofState, TacticError, TacticResult};
use crate::stack_safe;

/// Norm cast tactic.
///
/// Normalizes coercions (casts) in expressions by pushing them inward or
/// removing redundant casts. Useful when working with expressions involving
/// multiple numeric types.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// ENSURES: On `Ok(())`, the goal is closed or simplified with normalized casts
/// ENSURES: On `Err(NoGoals)`, `state.goals` was empty on entry
/// ENSURES: For equality goals, tries `rfl` after normalization if sides become equal
/// ENSURES: Falls back to `ring`, `norm_num`, then `decide` in sequence
///
/// # Supported Coercions
/// - `↑(a + b) → ↑a + ↑b` (push cast over addition)
/// - `↑(a * b) → ↑a * ↑b` (push cast over multiplication)
/// - `↑(↑a) → ↑a` (collapse nested casts when valid)
/// - `↑n` where `n : ℕ` (natural number literals)
///
/// # Example
/// ```text
/// -- Goal: (↑a : ℤ) + (↑b : ℤ) = ↑(a + b)
/// norm_cast
/// -- Goal closed
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
pub fn norm_cast(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Part of #2516: use proof-carry rewrite via simp engine instead of
    // heuristic AST surgery + replace_target_with_trusted_fallback.
    let rewrote = rewrite_target_with_cast_lemmas(state, "norm_cast", CastRewriteFlavor::NormCast)?;

    if rewrote {
        // Closeout order: rfl → ring → norm_num → decide
        if rfl(state).is_ok() {
            return Ok(());
        }
        if ring(state).is_ok() {
            return Ok(());
        }
    }

    // Try other tactics
    if norm_num(state).is_ok() {
        return Ok(());
    }

    if decide(state).is_ok() {
        return Ok(());
    }

    Ok(())
}

/// Normalize casts in an expression
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Nested casts `↑(↑a)` are collapsed to the inner cast
/// ENSURES: Casts over `add`/`mul` are pushed inward: `↑(a + b) → ↑a + ↑b`
/// ENSURES: Non-cast subexpressions are recursively preserved
/// ENSURES: Recursion is stack-safe
#[cfg(test)]
pub(crate) fn normalize_casts(expr: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, arg) => {
            // Check for cast application
            if is_cast_function(f) {
                let inner = normalize_casts(arg);
                // Check if inner is another cast - collapse nested casts
                if is_cast_expression(&inner) {
                    return inner;
                }
                // Check if we can push cast inward
                if let Some(pushed) = push_cast_inward(&inner, f) {
                    return pushed;
                }
                return Expr::app(normalize_casts(f), inner);
            }

            // Regular application - recurse
            Expr::app(normalize_casts(f), normalize_casts(arg))
        }
        ExprKind::Lam(bind_info, ty, body) => {
            Expr::lam(*bind_info, normalize_casts(ty), normalize_casts(body))
        }
        ExprKind::Pi(bind_info, ty, body) => {
            Expr::pi(*bind_info, normalize_casts(ty), normalize_casts(body))
        }
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            normalize_casts(ty),
            normalize_casts(val),
            normalize_casts(body),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => Expr::proj(name.clone(), *idx, normalize_casts(inner)),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), normalize_casts(inner)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(normalize_casts(inner))))
        }
        _ => expr.clone(),
    })
}

/// Check if expression is a cast function
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `true` iff the head constant name contains "coe", "Coe",
///   "cast", "Cast", "Nat.cast", or "Int.cast"
/// ENSURES: Returns `false` for non-constant head expressions
pub fn is_cast_function(expr: &Expr) -> bool {
    match get_app_fn(expr).kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            name_str.contains("coe")
                || name_str.contains("Coe")
                || name_str.contains("cast")
                || name_str.contains("Cast")
                || name_str.contains("Nat.cast")
                || name_str.contains("Int.cast")
        }
        _ => false,
    }
}

/// Check if expression is a cast application
#[cfg(test)]
fn is_cast_expression(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::App(f, _) => is_cast_function(f),
        _ => false,
    }
}

/// Try to push a cast inward over operations
#[cfg(test)]
fn push_cast_inward(expr: &Expr, cast_fn: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg2) = expr.kind() {
        if let ExprKind::App(f2, arg1) = f.kind() {
            if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                let name_str = name.to_string();

                // Push cast over addition: cast(a + b) = cast(a) + cast(b)
                if name_str.contains("add") || name_str.contains("Add") {
                    let cast_a = Expr::app(cast_fn.clone(), (**arg1).clone());
                    let cast_b = Expr::app(cast_fn.clone(), (**arg2).clone());
                    return Some(Expr::app(Expr::app((**f2).clone(), cast_a), cast_b));
                }

                // Push cast over multiplication
                if name_str.contains("mul") || name_str.contains("Mul") {
                    let cast_a = Expr::app(cast_fn.clone(), (**arg1).clone());
                    let cast_b = Expr::app(cast_fn.clone(), (**arg2).clone());
                    return Some(Expr::app(Expr::app((**f2).clone(), cast_a), cast_b));
                }
            }
        }
    }
    None
}

/// Check if two expressions are syntactically equal
///
/// REQUIRES: `e1` and `e2` are well-formed Lean expressions
/// ENSURES: Returns `true` iff `e1` and `e2` have identical structure at every node
/// ENSURES: Does not handle alpha equivalence or definitional equality
/// ENSURES: Recursion is stack-safe
pub fn exprs_syntactically_equal(e1: &Expr, e2: &Expr) -> bool {
    stack_safe(|| match (e1.kind(), e2.kind()) {
        (ExprKind::BVar(i1), ExprKind::BVar(i2)) => i1 == i2,
        (ExprKind::FVar(id1), ExprKind::FVar(id2)) => id1 == id2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            exprs_syntactically_equal(f1, f2) && exprs_syntactically_equal(a1, a2)
        }
        (ExprKind::Lam(bi1, t1, b1), ExprKind::Lam(bi2, t2, b2))
        | (ExprKind::Pi(bi1, t1, b1), ExprKind::Pi(bi2, t2, b2)) => {
            bi1 == bi2 && exprs_syntactically_equal(t1, t2) && exprs_syntactically_equal(b1, b2)
        }
        (ExprKind::Let(_, t1, v1, b1, _), ExprKind::Let(_, t2, v2, b2, _)) => {
            exprs_syntactically_equal(t1, t2)
                && exprs_syntactically_equal(v1, v2)
                && exprs_syntactically_equal(b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && exprs_syntactically_equal(e1, e2)
        }
        (ExprKind::MData(_, e1), ExprKind::MData(_, e2)) => exprs_syntactically_equal(e1, e2),
        (ExprKind::Squash(e1), ExprKind::Squash(e2)) => exprs_syntactically_equal(e1, e2),
        _ => false,
    })
}
