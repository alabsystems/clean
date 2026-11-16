// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural pattern extractors for the TLA+ encoding.
//!
//! Every function here is a *destructor*: it recognises one encoded shape
//! (`TLA.eq`, `Not`, `Or`, `TLA.forallIn`, a `Nat.succ` chain, ...) and hands
//! back its components, or `None` when the shape does not match. The
//! predicates and constructors those extractors are paired with live in the
//! parent [`super`] module.

use clean_kernel::{Expr, ExprKind};

use super::is_nat_type;

/// Extract inner expression from Nat.succ(x) -> Some(x)
pub(crate) fn extract_succ(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Nat.succ" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Extract equality from goal (Eq or TLA.eq)
pub(crate) fn extract_equality(goal: &Expr) -> Option<(Expr, Expr)> {
    // Pattern 1: Eq ty lhs rhs
    // Pattern 2: App(App(TLA.eq, lhs), rhs)
    if let ExprKind::App(f, rhs) = goal.kind() {
        if let ExprKind::App(f2, lhs) = f.kind() {
            // Check for Eq _ lhs rhs
            if let ExprKind::App(eq, _ty) = f2.kind() {
                if let ExprKind::Const(name, _) = eq.kind() {
                    if name.to_string() == "Eq" {
                        return Some(((**lhs).clone(), (**rhs).clone()));
                    }
                }
            }
            // Check for TLA.eq lhs rhs
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "TLA.eq" {
                    return Some(((**lhs).clone(), (**rhs).clone()));
                }
            }
        }
    }
    None
}

/// Extract binary arithmetic operation: returns (op_name, arg1, arg2)
pub(crate) fn extract_binary_arith(expr: &Expr) -> Option<(String, Expr, Expr)> {
    if let ExprKind::App(f, arg2) = expr.kind() {
        if let ExprKind::App(op, arg1) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                return Some((name.to_string(), (**arg1).clone(), (**arg2).clone()));
            }
        }
    }
    None
}

/// Extract P and Q from implication P -> Q.
///
/// Implications can be encoded as:
/// 1. Or(Not(P), Q) - classical encoding
/// 2. Pi(_, P, Q) where Q doesn't depend on the binding - non-dependent implication
pub fn extract_implication(expr: &Expr) -> Option<(Expr, Expr)> {
    // First try: non-dependent Pi encoding (P -> Q as Pi(_, P, Q))
    if let ExprKind::Pi(_, ty, body) = expr.kind() {
        if !body.has_loose_bvars() {
            return Some(((**ty).clone(), (**body).clone()));
        }
    }

    // Second try: Or(Not(P), Q) encoding
    if let Some((left, right)) = extract_or(expr) {
        if let Some(p) = extract_not(&left) {
            return Some((p, right));
        }
    }

    None
}

/// Extract P from Not(P)
pub fn extract_not(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Not" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Extract P and Q from Or(P, Q)
pub fn extract_or(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f, q) = expr.kind() {
        if let ExprKind::App(or, p) = f.kind() {
            if let ExprKind::Const(name, _) = or.kind() {
                if name.to_string() == "Or" {
                    return Some(((**p).clone(), (**q).clone()));
                }
            }
        }
    }
    None
}

/// Extract comparison from expression: returns (op, lhs, rhs)
/// Pattern: App(App(TLA.op, lhs), rhs) where op is gt/lt/ge/le
pub fn extract_comparison(expr: &Expr) -> Option<(String, Expr, Expr)> {
    if let ExprKind::App(f, rhs) = expr.kind() {
        if let ExprKind::App(op, lhs) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                let name_str = name.to_string();
                if let Some(op_name) = name_str.strip_prefix("TLA.") {
                    if matches!(op_name, "gt" | "lt" | "ge" | "le") {
                        return Some((op_name.to_string(), (**lhs).clone(), (**rhs).clone()));
                    }
                }
            }
        }
    }
    None
}

/// Extract the body of a forall over Nat.
///
/// Returns Some(body) if goal has form `forall n : Nat, P(n)` (Pi over Nat).
/// The body contains BVar(0) which refers to the bound variable.
pub fn extract_forall_nat(goal: &Expr) -> Option<Expr> {
    if let ExprKind::Pi(_, ty, body) = goal.kind() {
        if is_nat_type(ty) {
            return Some((**body).clone());
        }
    }
    None
}

/// Extract (set, var_name, body) from TLA.forallIn S (lambda x. P(x))
pub fn extract_tla_forall_in(goal: &Expr) -> Option<(Expr, String, Expr)> {
    // Pattern: App(App(TLA.forallIn, set), lambda)
    if let ExprKind::App(f, lambda) = goal.kind() {
        if let ExprKind::App(forall_in, set) = f.kind() {
            if let ExprKind::Const(name, _) = forall_in.kind() {
                if name.to_string() == "TLA.forallIn" {
                    // Extract the lambda body
                    if let ExprKind::Lam(_, _, body) = lambda.kind() {
                        // For now, use a placeholder name since Lam doesn't store it
                        return Some(((**set).clone(), "_x".to_string(), (**body).clone()));
                    }
                }
            }
        }
    }
    None
}

/// Check if expression is a product type (A x B)
///
/// Returns Some((A, B)) if it's a product type.
pub fn extract_product_type(expr: &Expr) -> Option<(Expr, Expr)> {
    // Pattern: App(App(Prod, A), B)
    if let ExprKind::App(f, b) = expr.kind() {
        if let ExprKind::App(prod, a) = f.kind() {
            if let ExprKind::Const(name, _) = prod.kind() {
                let name_str = name.to_string();
                if name_str == "Prod" || name_str == "TLA.Prod" {
                    return Some(((**a).clone(), (**b).clone()));
                }
            }
        }
    }
    None
}

/// Extract a natural number literal from an expression.
pub fn extract_nat_lit(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64(),
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if s == "Nat.zero" || s == "TLA.zero" || s == "Int.zero" {
                Some(0)
            } else {
                None
            }
        }
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return extract_nat_lit(arg).map(|n| n + 1);
                }
                // Handle Int.ofNat and TLA.int wrappers
                if s == "Int.ofNat" || s == "TLA.int" {
                    return extract_nat_lit(arg);
                }
            }
            None
        }
        _ => None,
    }
}
