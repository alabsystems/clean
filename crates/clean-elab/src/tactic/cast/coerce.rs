// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Numeric type coercion tactics — zify (ℕ→ℤ) and qify (ℤ→ℚ).

#[cfg(test)]
use std::sync::Arc;

#[cfg(test)]
use clean_kernel::expr::ExprKind;
#[cfg(test)]
use clean_kernel::name::Name;
#[cfg(test)]
use clean_kernel::Expr;

#[cfg(test)]
use crate::stack_safe;
use crate::tactic::{ProofState, TacticError, TacticResult};

use super::proof_carry::{rewrite_target_with_cast_lemmas, CastRewriteFlavor};

/// Convert natural number goals to integer goals.
///
/// `zify` rewrites propositions involving natural numbers to equivalent
/// propositions involving integers, introducing appropriate casts.
///
/// # Transformations
/// - `(a : ℕ) ≤ b` → `(↑a : ℤ) ≤ ↑b`
/// - `(a : ℕ) < b` → `(↑a : ℤ) < ↑b`
/// - `(a : ℕ) = b` → `(↑a : ℤ) = ↑b`
/// - `a - b` (truncated) → `↑a - ↑b` (proper subtraction)
///
/// This is useful when natural number arithmetic would lose information
/// due to truncation.
///
/// # Example
/// ```text
/// -- Goal: a - b ≤ c (in ℕ)
/// zify
/// -- Goal: (↑a : ℤ) - ↑b ≤ ↑c
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal target has Nat operations replaced with
///   Int equivalents (e.g., truncated subtraction becomes proper subtraction).
/// ENSURES: Returns `Err(NoProgress)` when no Nat-to-Int transformations apply.
pub fn zify(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Part of #2516: use proof-carry rewrite via simp engine instead of
    // heuristic AST surgery + replace_target_with_trusted_fallback.
    // Unsupported shapes (Nat.sub without side-condition proof) return NoProgress.
    let rewrote = rewrite_target_with_cast_lemmas(state, "zify", CastRewriteFlavor::Zify)?;

    if !rewrote {
        return Err(TacticError::NoProgress {
            tactic: "zify".into(),
        });
    }

    Ok(())
}

/// Transform natural number expressions to integer expressions
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Nat.sub/HSub.hSub on Nat operands are wrapped with Int.ofNat casts.
/// ENSURES: Returns a structurally equivalent expression; unchanged sub-trees are cloned.
#[cfg(test)]
pub(crate) fn zify_expr(expr: &Expr, state: &mut ProofState) -> Expr {
    // Check for Nat type annotations and convert to Int
    match expr.kind() {
        ExprKind::App(func, arg) => {
            let func_z = zify_expr(func, state);
            let arg_z = zify_expr(arg, state);

            // Check if this is a Nat operation that should become Int
            if let ExprKind::Const(name, _) = func_z.kind() {
                let name_str = name.to_string();
                // Convert Nat.sub to Int.sub (which doesn't truncate)
                if name_str == "Nat.sub" || name_str == "HSub.hSub" {
                    // Check if operating on Nat
                    if is_nat_expr(&arg_z) {
                        // Insert Int cast; Int.ofNat is not universe-polymorphic
                        let int_name = Name::from_string("Int");
                        let cast = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
                        return Expr::app(
                            Expr::app(
                                state.mk_const_str("HSub.hSub"),
                                Expr::app(cast.clone(), arg_z),
                            ),
                            Expr::const_(int_name, vec![]),
                        );
                    }
                }
            }

            Expr::app(func_z, arg_z)
        }

        ExprKind::Lam(bi, binder_type, body) => {
            Expr::lam(*bi, zify_expr(binder_type, state), zify_expr(body, state))
        }

        ExprKind::Pi(bi, binder_type, body) => {
            Expr::pi(*bi, zify_expr(binder_type, state), zify_expr(body, state))
        }

        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            zify_expr(ty, state),
            zify_expr(val, state),
            zify_expr(body, state),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => Expr::proj(name.clone(), *idx, zify_expr(inner, state)),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), zify_expr(inner, state)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(zify_expr(inner, state))))
        }

        _ => expr.clone(),
    }
}

/// Check if an expression has Nat type (heuristic)
#[cfg(test)]
pub(crate) fn is_nat_expr(expr: &Expr) -> bool {
    stack_safe(|| match expr.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            s == "Nat" || s.starts_with("Nat.")
        }
        ExprKind::App(func, _) => is_nat_expr(func),
        _ => false,
    })
}

/// Convert integer goals to rational goals.
///
/// `qify` rewrites propositions involving integers to equivalent
/// propositions involving rationals, introducing appropriate casts.
///
/// # Transformations
/// - `(a : ℤ) ≤ b` → `(↑a : ℚ) ≤ ↑b`
/// - `a / b` (truncated) → `↑a / ↑b` (exact division)
///
/// # Example
/// ```text
/// -- Goal: a / b = c (in ℤ)
/// qify
/// -- Goal: (↑a : ℚ) / ↑b = ↑c
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal target has Int operations replaced with
///   Rat equivalents (e.g., truncated division becomes exact division).
/// ENSURES: Returns `Err(NoProgress)` when no Int-to-Rat transformations apply.
pub fn qify(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Part of #2516: use proof-carry rewrite via simp engine instead of
    // heuristic AST surgery + replace_target_with_trusted_fallback.
    // Unsupported shapes (Int.div without side-condition proof) return NoProgress.
    let rewrote = rewrite_target_with_cast_lemmas(state, "qify", CastRewriteFlavor::Qify)?;

    if !rewrote {
        return Err(TacticError::NoProgress {
            tactic: "qify".into(),
        });
    }

    Ok(())
}

/// Transform integer expressions to rational expressions
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Int.div/HDiv.hDiv on Int operands are wrapped with Rat.ofInt casts.
/// ENSURES: Returns a structurally equivalent expression; unchanged sub-trees are cloned.
#[cfg(test)]
pub(crate) fn qify_expr(expr: &Expr, state: &mut ProofState) -> Expr {
    match expr.kind() {
        ExprKind::App(func, arg) => {
            let func_q = qify_expr(func, state);
            let arg_q = qify_expr(arg, state);

            // Check for Int division that should become Rat
            if let ExprKind::Const(name, _) = func_q.kind() {
                let name_str = name.to_string();
                if (name_str == "Int.div" || name_str == "HDiv.hDiv") && is_int_expr(&arg_q) {
                    // Rat.ofInt is not universe-polymorphic
                    let cast = Expr::const_(Name::from_string("Rat.ofInt"), vec![]);
                    return Expr::app(
                        Expr::app(
                            state.mk_const_str("HDiv.hDiv"),
                            Expr::app(cast.clone(), arg_q),
                        ),
                        Expr::const_(Name::from_string("Rat"), vec![]),
                    );
                }
            }

            Expr::app(func_q, arg_q)
        }

        ExprKind::Lam(bi, binder_type, body) => {
            Expr::lam(*bi, qify_expr(binder_type, state), qify_expr(body, state))
        }

        ExprKind::Pi(bi, binder_type, body) => {
            Expr::pi(*bi, qify_expr(binder_type, state), qify_expr(body, state))
        }

        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            qify_expr(ty, state),
            qify_expr(val, state),
            qify_expr(body, state),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => Expr::proj(name.clone(), *idx, qify_expr(inner, state)),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), qify_expr(inner, state)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(qify_expr(inner, state))))
        }

        _ => expr.clone(),
    }
}

/// Check if an expression has Int type (heuristic)
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `true` when the head constant is "Int" or starts with "Int.".
#[cfg(test)]
pub(crate) fn is_int_expr(expr: &Expr) -> bool {
    stack_safe(|| match expr.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            s == "Int" || s.starts_with("Int.")
        }
        ExprKind::App(func, _) => is_int_expr(func),
        _ => false,
    })
}
