// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared utility functions used across pattern tactic submodules.

use crate::stack_safe;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::super::LocalDecl;

/// Check if two expressions are structurally equal
///
/// REQUIRES: `a` and `b` are well-formed expressions
/// ENSURES: Returns `true` only for structural equality; performs no reduction or definitional equality
pub(crate) fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    stack_safe(|| match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(f1), ExprKind::FVar(f2)) => f1 == f2,
        (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            exprs_equal(f1, f2) && exprs_equal(a1, a2)
        }
        (ExprKind::Lam(b1, t1, bo1), ExprKind::Lam(b2, t2, bo2))
        | (ExprKind::Pi(b1, t1, bo1), ExprKind::Pi(b2, t2, bo2)) => {
            b1 == b2 && exprs_equal(t1, t2) && exprs_equal(bo1, bo2)
        }
        (ExprKind::Let(_, t1, v1, bo1, _), ExprKind::Let(_, t2, v2, bo2, _)) => {
            exprs_equal(t1, t2) && exprs_equal(v1, v2) && exprs_equal(bo1, bo2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && exprs_equal(e1, e2)
        }
        (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2))
        | (ExprKind::Squash(inner1), ExprKind::Squash(inner2)) => exprs_equal(inner1, inner2),
        _ => false,
    })
}

/// Make a relation expression from relation name and arguments.
///
/// Builds `@Rel.{u} ty inst lhs rhs` -- the fully-applied form required by the
/// kernel. For "eq", builds `@Eq.{u} ty lhs rhs` (Eq has no instance arg).
///
/// Part of #2078: previously only produced `Rel lhs rhs` (missing type + instance
/// and using empty universe levels).
///
/// REQUIRES: `ty` and `inst` correspond to the relation arguments when `rel_name != "eq"`
/// ENSURES: Returns a fully applied relation term with explicit type arguments
/// ENSURES: Special-cases equality to omit an instance argument
#[cfg(test)]
pub(crate) fn make_relation(
    rel_name: &str,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    state: &mut super::super::ProofState,
) -> Expr {
    let rel_const_name = match rel_name {
        "le" => "LE.le",
        "lt" => "LT.lt",
        "ge" => "GE.ge",
        "gt" => "GT.gt",
        "eq" => "Eq",
        _ => rel_name,
    };

    if rel_name == "eq" {
        // Eq has 3 args: type, lhs, rhs (no instance)
        Expr::app(
            Expr::app(
                Expr::app(state.mk_const_str(rel_const_name), ty.clone()),
                lhs.clone(),
            ),
            rhs.clone(),
        )
    } else {
        // Comparison relations: 4 args with type + instance
        super::super::tc_app::mk_tc_rel(
            state.mk_const_str(rel_const_name),
            ty.clone(),
            inst.clone(),
            lhs.clone(),
            rhs.clone(),
        )
    }
}

/// Check if expression is a binary application of a specific function
///
/// ENSURES: Returns `true` iff `expr` is an application chain with at least two args and head const `func_name`
#[cfg(test)]
pub(crate) fn is_binary_app(expr: &Expr, func_name: &str) -> bool {
    // Pattern: f a b (two applications)
    if let ExprKind::App(f1, _) = expr.kind() {
        if let ExprKind::App(f2, _) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                return name.to_string() == func_name;
            }
            // Could be more applications (with type args)
            let mut current = f2.as_ref();
            while let ExprKind::App(inner, _) = current.kind() {
                current = inner.as_ref();
            }
            if let ExprKind::Const(name, _) = current.kind() {
                return name.to_string() == func_name;
            }
        }
    }
    false
}

/// Extract arguments from a binary application
///
/// REQUIRES: `expr` is an application chain with at least two arguments
/// ENSURES: On Ok, returns the final two arguments in application order
/// ENSURES: On Err, `expr` did not contain two application arguments
#[cfg(test)]
pub(crate) fn extract_binary_args(expr: &Expr) -> Result<(Expr, Expr), super::super::TacticError> {
    // Get the last two arguments
    let mut args = Vec::new();
    let mut current = expr;

    while let ExprKind::App(f, arg) = current.kind() {
        args.push(arg.as_ref().clone());
        current = f;
    }

    args.reverse();

    if args.len() >= 2 {
        let n = args.len();
        Ok((args[n - 2].clone(), args[n - 1].clone()))
    } else {
        Err(super::super::TacticError::InvalidTarget {
            tactic: "mono".into(),
            detail: "expected binary application".into(),
        })
    }
}

/// Get the head of an application chain
///
/// ENSURES: Returns the leftmost non-`App` head of `expr`
pub(crate) fn get_app_head(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::App(f, _) = current.kind() {
        current = f;
    }
    current
}

/// Generate a fresh hypothesis name not already in the context
///
/// ENSURES: Returned name does not collide with any `LocalDecl.name` in `ctx`
/// ENSURES: Returns `base` unchanged when it is not already used
pub(crate) fn generate_fresh_hyp_name(ctx: &[LocalDecl], base: &str) -> String {
    let existing: std::collections::HashSet<_> = ctx.iter().map(|d| d.name.clone()).collect();

    if !existing.contains(base) {
        return base.to_string();
    }

    for i in 1.. {
        let name = format!("{base}{i}");
        if !existing.contains(&name) {
            return name;
        }
    }

    // Should never reach here
    format!("{}_{}", base, std::process::id())
}

/// Try to extract existential type: exists x : A, P x -> Some((A, lambda x, P x))
///
/// ENSURES: Returns `Some(domain, pred)` only for `Exists`, `Sigma`, or `PSigma` applications
pub(crate) fn try_extract_exists(expr: &Expr) -> Option<(Expr, Expr)> {
    // Exists is: App(App(Exists, A), P) where P : A -> Prop
    if let ExprKind::App(f, pred) = expr.kind() {
        if let ExprKind::App(exists_const, domain) = f.kind() {
            if let ExprKind::Const(name, _) = exists_const.kind() {
                let name_str = name.to_string();
                if name_str == "Exists" || name_str.ends_with(".Exists") {
                    return Some((domain.as_ref().clone(), pred.as_ref().clone()));
                }
            }
        }
    }

    // Also handle Sigma types for type-level existentials
    if let ExprKind::App(f, pred) = expr.kind() {
        if let ExprKind::App(sigma_const, domain) = f.kind() {
            if let ExprKind::Const(name, _) = sigma_const.kind() {
                let name_str = name.to_string();
                if name_str == "Sigma" || name_str == "PSigma" || name_str.ends_with(".Sigma") {
                    return Some((domain.as_ref().clone(), pred.as_ref().clone()));
                }
            }
        }
    }

    None
}

/// Apply a predicate (lambda) to an argument
///
/// ENSURES: If `pred` is a lambda, substitutes `arg` for `BVar(0)` in the body
/// ENSURES: Otherwise returns the ordinary application `pred arg`
pub(crate) fn apply_predicate(pred: &Expr, arg: Expr) -> Expr {
    match pred.kind() {
        ExprKind::Lam(_, _, body) => {
            // Delegate to kernel's ExprFolderOpt-based instantiate (#2141)
            body.instantiate(&arg)
        }
        _ => {
            // Just apply if not a lambda
            Expr::app(pred.clone(), arg)
        }
    }
}

/// Extract the type class name from a type
///
/// ENSURES: Returns the head constant name of `ty` when one exists through nested applications
pub(crate) fn extract_class_name(ty: &Expr) -> Option<String> {
    stack_safe(|| match ty.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::App(f, _) => extract_class_name(f),
        _ => None,
    })
}

/// Check if expression is True
///
/// ENSURES: Returns `true` only for `True` constants (including namespaced forms)
pub(crate) fn is_true_prop(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let s = name.to_string();
        s == "True" || s.ends_with(".True")
    } else {
        false
    }
}

/// Check if expression is False
///
/// ENSURES: Returns `true` only for `False` constants (including namespaced forms)
pub(crate) fn is_false_prop(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let s = name.to_string();
        s == "False" || s.ends_with(".False")
    } else {
        false
    }
}

/// Try to extract equality: Eq a b -> Some((a, b))
///
/// ENSURES: Returns `Some(lhs, rhs)` only for fully applied `Eq` expressions
pub(crate) fn try_extract_eq(expr: &Expr) -> Option<(Expr, Expr)> {
    // Eq is App(App(App(Eq, ty), a), b)
    if let ExprKind::App(f1, b) = expr.kind() {
        if let ExprKind::App(f2, a) = f1.kind() {
            if let ExprKind::App(eq_const, _ty) = f2.kind() {
                if let ExprKind::Const(name, _) = eq_const.kind() {
                    let s = name.to_string();
                    if s == "Eq" || s.ends_with(".Eq") {
                        return Some((a.as_ref().clone(), b.as_ref().clone()));
                    }
                }
            }
        }
    }
    None
}

/// Simple type inference for instance resolution
///
/// ENSURES: Returns only literal-based builtin types currently recognized by this heuristic
pub(crate) fn infer_simple_type(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::Lit(lit) => {
            // Infer type from literal
            match lit {
                clean_kernel::Literal::Nat(_) => {
                    Some(Expr::const_(Name::from_string("Nat"), vec![]))
                }
                clean_kernel::Literal::String(_) => {
                    Some(Expr::const_(Name::from_string("String"), vec![]))
                }
            }
        }
        _ => None, // Const and other cases would need environment lookup
    }
}

/// Try to infer the type of an expression (simple heuristics)
///
/// ENSURES: Returns a heuristic builtin type when it can be inferred without environment lookup
/// ENSURES: May return `None` for expressions whose type is otherwise inferable by the kernel
pub(crate) fn try_infer_expr_type(expr: &Expr) -> Option<Expr> {
    stack_safe(|| match expr.kind() {
        ExprKind::Lit(lit) => match lit {
            clean_kernel::Literal::Nat(_) => Some(Expr::const_(Name::from_string("Nat"), vec![])),
            clean_kernel::Literal::String(_) => {
                Some(Expr::const_(Name::from_string("String"), vec![]))
            }
        },
        ExprKind::Const(name, levels) => {
            // If it's a type constant, return it
            let s = name.to_string();
            if s == "Nat" || s == "Int" || s == "Bool" || s == "String" {
                return Some(Expr::const_(name.clone(), levels.clone()));
            }
            None
        }
        ExprKind::App(f, _) => {
            // Try to get the result type
            try_infer_expr_type(f)
        }
        _ => None,
    })
}

/// Find the first type-like expression in an expression tree
///
/// ENSURES: Returns the first builtin type constant reachable by this depth-first traversal
pub(crate) fn find_first_type(expr: &Expr) -> Option<Expr> {
    stack_safe(|| match expr.kind() {
        ExprKind::Const(name, levels) => {
            let s = name.to_string();
            // Common types
            if matches!(
                s.as_str(),
                "Nat" | "Int" | "Bool" | "String" | "Float" | "Char"
            ) {
                return Some(Expr::const_(name.clone(), levels.clone()));
            }
            None
        }
        ExprKind::App(f, arg) => find_first_type(f).or_else(|| find_first_type(arg)),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            find_first_type(ty).or_else(|| find_first_type(body))
        }
        ExprKind::Let(_, ty, val, body, _) => find_first_type(ty)
            .or_else(|| find_first_type(val))
            .or_else(|| find_first_type(body)),
        _ => None,
    })
}
