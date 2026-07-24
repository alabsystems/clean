// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Free Variable Analysis and FVar Reference Checking
//!
//! Provides functions to compute free variables in LCNF code blocks and
//! check whether code references specific FVarIds. Used by the lambda
//! lifting transform to determine which variables need to be captured.

use crate::lcnf::{Alt, Arg, Code, LetValue};
use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use clean_kernel::{Expr, FVarId};
use std::collections::HashSet;

// ════════════════════════════════════════════════════════════════════════════
// Free Variable Analysis
// ════════════════════════════════════════════════════════════════════════════

/// Compute free variables in a Code block.
///
/// A variable is "free" if it's referenced but not bound in the given scope.
///
/// # Returns
///
/// Set of FVarIds that are referenced but not bound locally.
///
/// # Example
///
/// ```text
/// fun f (x : Nat) :=
///   let y := x + z  // z is free (not bound in f)
///   return y
/// ```
pub fn free_vars_in_code(code: &Code, bound: &HashSet<FVarId>) -> HashSet<FVarId> {
    let mut free = HashSet::new();
    collect_free_vars(code, bound, &mut free);
    free
}

/// Collect free variables from code, given a set of bound variables.
fn collect_free_vars(code: &Code, bound: &HashSet<FVarId>, free: &mut HashSet<FVarId>) {
    match code {
        Code::Return(fvar) => {
            if !bound.contains(fvar) {
                free.insert(*fvar);
            }
        }

        Code::Let(decl, body) => {
            // Collect from the let value and type annotation
            collect_free_vars_from_value(&decl.value, bound, free);
            collect_free_vars_from_expr(&decl.ty, bound, free);

            // The let-bound variable is now in scope for the body
            let mut new_bound = bound.clone();
            new_bound.insert(decl.fvar_id);
            collect_free_vars(body, &new_bound, free);
        }

        Code::Fun(fun_decl, body) => {
            // The function name is bound in the continuation
            let mut new_bound = bound.clone();
            new_bound.insert(fun_decl.fvar_id);

            // Collect from parameter types and return type (in outer scope)
            for param in &fun_decl.params {
                collect_free_vars_from_expr(&param.ty, bound, free);
            }
            collect_free_vars_from_expr(&fun_decl.ty, bound, free);

            // Add function parameters AND function name as bound in the function body
            // (function name needed for recursive references)
            let mut param_bound = bound.clone();
            param_bound.insert(fun_decl.fvar_id); // Allow recursive self-reference
            for param in &fun_decl.params {
                param_bound.insert(param.fvar_id);
            }

            // Collect from function body
            collect_free_vars(&fun_decl.body, &param_bound, free);

            // Collect from continuation
            collect_free_vars(body, &new_bound, free);
        }

        Code::JoinPoint(jp_decl, body) => {
            // Similar to Fun
            let mut new_bound = bound.clone();
            new_bound.insert(jp_decl.fvar_id);

            // Collect from parameter types and return type (in outer scope)
            for param in &jp_decl.params {
                collect_free_vars_from_expr(&param.ty, bound, free);
            }
            collect_free_vars_from_expr(&jp_decl.ty, bound, free);

            // Join point name and params are bound in its body
            let mut param_bound = bound.clone();
            param_bound.insert(jp_decl.fvar_id); // Allow recursive self-reference
            for param in &jp_decl.params {
                param_bound.insert(param.fvar_id);
            }

            collect_free_vars(&jp_decl.body, &param_bound, free);
            collect_free_vars(body, &new_bound, free);
        }

        Code::Cases(cases) => {
            // Scrutinee must be in scope
            if !bound.contains(&cases.scrutinee) {
                free.insert(cases.scrutinee);
            }
            collect_free_vars_from_expr(&cases.result_type, bound, free);

            // Collect from each alternative
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { params, body, .. } => {
                        // Constructor parameters are bound in the body
                        let mut alt_bound = bound.clone();
                        for param in params {
                            alt_bound.insert(param.fvar_id);
                        }
                        collect_free_vars(body, &alt_bound, free);
                    }
                    Alt::Default(body) => {
                        collect_free_vars(body, bound, free);
                    }
                }
            }
        }

        Code::Jmp { jp, args } => {
            // The join point itself is a reference
            if !bound.contains(jp) {
                free.insert(*jp);
            }
            // Collect from arguments
            for arg in args {
                collect_free_vars_from_arg(arg, bound, free);
            }
        }

        Code::Unreachable(expr) => {
            collect_free_vars_from_expr(expr, bound, free);
        }
    }
}

/// Collect free variables from a LetValue.
fn collect_free_vars_from_value(
    value: &LetValue,
    bound: &HashSet<FVarId>,
    free: &mut HashSet<FVarId>,
) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}

        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                collect_free_vars_from_arg(arg, bound, free);
            }
        }

        LetValue::Proj { structure, .. } => {
            if !bound.contains(structure) {
                free.insert(*structure);
            }
        }

        LetValue::FVar { fvar, args } => {
            if !bound.contains(fvar) {
                free.insert(*fvar);
            }
            for arg in args {
                collect_free_vars_from_arg(arg, bound, free);
            }
        }

        LetValue::Reuse { slot, args, .. } => {
            if !bound.contains(slot) {
                free.insert(*slot);
            }
            for arg in args {
                collect_free_vars_from_arg(arg, bound, free);
            }
        }
    }
}

/// Collect free variables from an Arg.
fn collect_free_vars_from_arg(arg: &Arg, bound: &HashSet<FVarId>, free: &mut HashSet<FVarId>) {
    match arg {
        Arg::FVar(fvar) => {
            if !bound.contains(fvar) {
                free.insert(*fvar);
            }
        }
        Arg::Type(expr) => {
            collect_free_vars_from_expr(expr, bound, free);
        }
        Arg::Erased | Arg::Index(_) => {}
    }
}

/// Collect free variables from an expression (conservative).
///
/// This is a simplified analysis that treats any FVarId in the expression as
/// potentially free. Full analysis would require understanding the expression
/// structure better.
pub(super) fn collect_free_vars_from_expr(
    expr: &Expr,
    bound: &HashSet<FVarId>,
    free: &mut HashSet<FVarId>,
) {
    // Walk the expression looking for FVar nodes
    match expr.kind() {
        ExprKind::FVar(fvar) if !bound.contains(fvar) => {
            free.insert(*fvar);
        }
        ExprKind::App(f, arg) => {
            collect_free_vars_from_expr(f, bound, free);
            collect_free_vars_from_expr(arg, bound, free);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_free_vars_from_expr(ty, bound, free);
            collect_free_vars_from_expr(body, bound, free);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_free_vars_from_expr(ty, bound, free);
            collect_free_vars_from_expr(val, bound, free);
            // Note: ExprKind::Let doesn't bind a variable (unlike Code::Let),
            // it's a let-expression in the term language. The bound variable
            // is implicit in de Bruijn indexing. For our conservative analysis,
            // we just traverse all subterms.
            collect_free_vars_from_expr(body, bound, free);
        }
        ExprKind::MData(_, inner)
        | ExprKind::Proj(_, _, inner)
        | ExprKind::Squash(inner)
        | ExprKind::CubicalPathLam { body: inner } => {
            collect_free_vars_from_expr(inner, bound, free);
        }
        ExprKind::CubicalPathApp { path, arg }
        | ExprKind::ZFCMem {
            element: path,
            set: arg,
        } => {
            collect_free_vars_from_expr(path, bound, free);
            collect_free_vars_from_expr(arg, bound, free);
        }
        ExprKind::CubicalPath { ty, left, right }
        | ExprKind::CubicalTransp {
            ty,
            phi: left,
            base: right,
        } => {
            collect_free_vars_from_expr(ty, bound, free);
            collect_free_vars_from_expr(left, bound, free);
            collect_free_vars_from_expr(right, bound, free);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            collect_free_vars_from_expr(ty, bound, free);
            collect_free_vars_from_expr(phi, bound, free);
            collect_free_vars_from_expr(u, bound, free);
            collect_free_vars_from_expr(base, bound, free);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            collect_free_vars_from_expr(domain, bound, free);
            collect_free_vars_from_expr(pred, bound, free);
        }
        ExprKind::ZFCSet(zfc) => match zfc {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
            ZFCSetExpr::Singleton(inner)
            | ZFCSetExpr::Union(inner)
            | ZFCSetExpr::PowerSet(inner)
            | ZFCSetExpr::Choice(inner) => {
                collect_free_vars_from_expr(inner, bound, free);
            }
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => {
                collect_free_vars_from_expr(a, bound, free);
                collect_free_vars_from_expr(b, bound, free);
            }
        },
        // Leaf variants: BVar, Sort, Const, Lit, SProp, CubicalInterval, CubicalI0, CubicalI1
        _ => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// FVar Reference Checking
// ════════════════════════════════════════════════════════════════════════════

/// Check if code references a specific FVarId.
///
/// Used to detect recursive functions (functions that reference themselves).
pub(super) fn code_references_fvar(code: &Code, target: FVarId) -> bool {
    match code {
        Code::Return(fvar) => *fvar == target,

        Code::Let(decl, body) => {
            value_references_fvar(&decl.value, target) || code_references_fvar(body, target)
        }

        Code::Fun(fun_decl, body) => {
            code_references_fvar(&fun_decl.body, target) || code_references_fvar(body, target)
        }

        Code::JoinPoint(jp_decl, body) => {
            code_references_fvar(&jp_decl.body, target) || code_references_fvar(body, target)
        }

        Code::Cases(cases) => {
            cases.scrutinee == target
                || expr_contains_fvar(&cases.result_type, target)
                || cases.alts.iter().any(|alt| match alt {
                    Alt::Ctor { body, .. } => code_references_fvar(body, target),
                    Alt::Default(body) => code_references_fvar(body, target),
                })
        }

        Code::Jmp { jp, args } => {
            *jp == target || args.iter().any(|arg| arg_references_fvar(arg, target))
        }

        Code::Unreachable(_) => false, // Don't check unreachable code
    }
}

/// Check if a LetValue references a specific FVarId.
fn value_references_fvar(value: &LetValue, target: FVarId) -> bool {
    match value {
        LetValue::Lit(_) | LetValue::Erased => false,
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            args.iter().any(|arg| arg_references_fvar(arg, target))
        }
        LetValue::Proj { structure, .. } => *structure == target,
        LetValue::FVar { fvar, args } => {
            *fvar == target || args.iter().any(|arg| arg_references_fvar(arg, target))
        }
        LetValue::Reuse { slot, args, .. } => {
            *slot == target || args.iter().any(|arg| arg_references_fvar(arg, target))
        }
    }
}

/// Check if an Arg references a specific FVarId.
fn arg_references_fvar(arg: &Arg, target: FVarId) -> bool {
    match arg {
        Arg::FVar(fvar) => *fvar == target,
        Arg::Type(expr) => expr_contains_fvar(expr, target),
        Arg::Erased | Arg::Index(_) => false,
    }
}

/// Check if an expression contains a reference to a specific FVarId.
fn expr_contains_fvar(expr: &Expr, target: FVarId) -> bool {
    match expr.kind() {
        ExprKind::FVar(fvar) => *fvar == target,
        ExprKind::App(f, arg) => expr_contains_fvar(f, target) || expr_contains_fvar(arg, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_fvar(ty, target) || expr_contains_fvar(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_fvar(ty, target)
                || expr_contains_fvar(val, target)
                || expr_contains_fvar(body, target)
        }
        ExprKind::MData(_, inner)
        | ExprKind::Proj(_, _, inner)
        | ExprKind::Squash(inner)
        | ExprKind::CubicalPathLam { body: inner } => expr_contains_fvar(inner, target),
        ExprKind::CubicalPathApp { path, arg }
        | ExprKind::ZFCMem {
            element: path,
            set: arg,
        } => expr_contains_fvar(path, target) || expr_contains_fvar(arg, target),
        ExprKind::CubicalPath { ty, left, right }
        | ExprKind::CubicalTransp {
            ty,
            phi: left,
            base: right,
        } => {
            expr_contains_fvar(ty, target)
                || expr_contains_fvar(left, target)
                || expr_contains_fvar(right, target)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_contains_fvar(ty, target)
                || expr_contains_fvar(phi, target)
                || expr_contains_fvar(u, target)
                || expr_contains_fvar(base, target)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_contains_fvar(domain, target) || expr_contains_fvar(pred, target)
        }
        ExprKind::ZFCSet(zfc) => match zfc {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
            ZFCSetExpr::Singleton(inner)
            | ZFCSetExpr::Union(inner)
            | ZFCSetExpr::PowerSet(inner)
            | ZFCSetExpr::Choice(inner) => expr_contains_fvar(inner, target),
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => {
                expr_contains_fvar(a, target) || expr_contains_fvar(b, target)
            }
        },
        // Leaf variants: BVar, Sort, Const, Lit, SProp, CubicalInterval, CubicalI0, CubicalI1
        _ => false,
    }
}
