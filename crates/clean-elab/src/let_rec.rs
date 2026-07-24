// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Let-rec elaboration utilities: recursion analysis and fixed-point encoding.
//!
//! Handles `let rec f := ... in ...` expressions by analyzing recursion
//! patterns and building fixed-point combinator terms. Lean 4 supports both
//! single and mutual `let rec` bindings, each of which may use structural
//! or well-founded recursion.
//!
//! # Architecture
//!
//! This module provides:
//! - Recursion analysis: detect whether a binding is recursive, and if so,
//!   classify as structural or well-founded
//! - Expression utilities: FVar replacement, occurrence counting
//! - Fixed-point term construction helpers
//!
//! The ElabCtx integration lives in `infer/elab_core.rs` where the private
//! fields of ElabCtx are accessible.
//!
//! # Desugaring
//!
//! A single `let rec f (n : Nat) : Nat := body in e` becomes:
//!
//! ```text
//! let f : (Nat → Nat) := @Nat.rec (fun _ => Nat) base step in e
//!   -- structural recursion on Nat
//! ```
//!
//! Or, when structural recursion is not detected:
//!
//! ```text
//! let f : (Nat → Nat) := WellFounded.fix ... in e
//!   -- well-founded recursion fallback
//! ```
//!
//! # Reference
//!
//! Lean 4: `src/Lean/Elab/LetRec.lean`

use clean_kernel::{Expr, ExprFolder, FVarId};
use clean_parser::{SurfaceBinder, SurfaceExpr};

use crate::stack_safe;

/// Classification of recursion strategy for a let-rec binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecursionStrategy {
    /// Structural recursion: a parameter decreases on an inductive type.
    Structural {
        /// 0-indexed position of the decreasing argument.
        decreasing_arg: usize,
    },
    /// Well-founded recursion: no structural decrease detected; use
    /// `WellFounded.fix` with a sorry-based measure.
    WellFounded,
    /// Non-recursive: the binding does not reference itself.
    NonRecursive,
}

/// Information about a single binding in a mutual let-rec block.
#[derive(Debug, Clone)]
pub(crate) struct LetRecEntry {
    /// Binding name (e.g., "f").
    pub(crate) name: String,
    /// Elaborated type.
    pub(crate) ty: Expr,
    /// FVarId used for forward references during elaboration.
    pub(crate) fvar: FVarId,
}

// =========================================================================
// Recursion detection
// =========================================================================

/// Detect whether a surface expression contains references to a given name,
/// indicating recursion.
pub(crate) fn contains_self_reference(expr: &SurfaceExpr, name: &str) -> bool {
    stack_safe(|| match expr {
        SurfaceExpr::Ident(_, ident) => ident == name,
        SurfaceExpr::App(_, func, args) => {
            contains_self_reference(func, name)
                || args.iter().any(|a| contains_self_reference(&a.expr, name))
        }
        SurfaceExpr::Lambda(_, binders, body) => {
            if binders.iter().any(|b| b.name == name) {
                return false; // shadowed
            }
            binders
                .iter()
                .filter_map(|b| b.ty.as_deref())
                .any(|ty| contains_self_reference(ty, name))
                || contains_self_reference(body, name)
        }
        SurfaceExpr::Pi(_, binders, body) => {
            if binders.iter().any(|b| b.name == name) {
                return false;
            }
            binders
                .iter()
                .filter_map(|b| b.ty.as_deref())
                .any(|ty| contains_self_reference(ty, name))
                || contains_self_reference(body, name)
        }
        SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
            let in_val = contains_self_reference(val, name);
            let in_ty = binder
                .ty
                .as_deref()
                .is_some_and(|ty| contains_self_reference(ty, name));
            let shadowed = binder.name == name;
            in_val || in_ty || (!shadowed && contains_self_reference(body, name))
        }
        SurfaceExpr::If(_, cond, t, f) => {
            contains_self_reference(cond, name)
                || contains_self_reference(t, name)
                || contains_self_reference(f, name)
        }
        SurfaceExpr::Match(_, _, scrut, arms) => {
            contains_self_reference(scrut, name)
                || arms
                    .iter()
                    .any(|arm| contains_self_reference(&arm.body, name))
        }
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Explicit(_, inner) => {
            contains_self_reference(inner, name)
        }
        SurfaceExpr::Ascription(_, inner, ty) => {
            contains_self_reference(inner, name) || contains_self_reference(ty, name)
        }
        SurfaceExpr::Arrow(_, from, to) => {
            contains_self_reference(from, name) || contains_self_reference(to, name)
        }
        SurfaceExpr::Do(_, elems) => elems
            .iter()
            .any(|e| contains_self_reference_do_elem(e, name)),
        SurfaceExpr::IfLet(_, _, scrutinee, then_br, else_br) => {
            contains_self_reference(scrutinee, name)
                || contains_self_reference(then_br, name)
                || contains_self_reference(else_br, name)
        }
        _ => false,
    })
}

/// Check do-notation elements for self-references.
fn contains_self_reference_do_elem(elem: &clean_parser::DoElem, name: &str) -> bool {
    match elem {
        clean_parser::DoElem::Expr(_, e) => contains_self_reference(e, name),
        clean_parser::DoElem::Let(_, _, val) => contains_self_reference(val, name),
        clean_parser::DoElem::LetMut(_, _, val) => contains_self_reference(val, name),
        clean_parser::DoElem::Bind(_, _, e) => contains_self_reference(e, name),
        clean_parser::DoElem::Return(_, e) => contains_self_reference(e, name),
        clean_parser::DoElem::LetRec(_, bindings) => bindings
            .iter()
            .any(|(_, val)| contains_self_reference(val, name)),
        _ => false,
    }
}

/// Classify the recursion strategy for a let-rec binding.
///
/// 1. If the value does not reference the binding name, returns `NonRecursive`.
/// 2. If structural recursion is detected (decreasing argument on inductive),
///    returns `Structural`.
/// 3. Otherwise returns `WellFounded`.
pub(crate) fn classify_recursion(
    name: &str,
    binder: &SurfaceBinder,
    val: &SurfaceExpr,
) -> RecursionStrategy {
    if !contains_self_reference(val, name) {
        return RecursionStrategy::NonRecursive;
    }

    // Attempt structural recursion: look for a match on a parameter.
    if let Some(dec_arg) = detect_structural_param(name, val) {
        return RecursionStrategy::Structural {
            decreasing_arg: dec_arg,
        };
    }

    // Attempt structural from type annotation (known inductive types).
    if let Some(ty_expr) = &binder.ty {
        if let Some(dec_arg) = detect_structural_from_type(ty_expr) {
            return RecursionStrategy::Structural {
                decreasing_arg: dec_arg,
            };
        }
    }

    RecursionStrategy::WellFounded
}

/// Try to detect a structurally decreasing parameter by examining the
/// value's lambda binders and match expressions.
fn detect_structural_param(func_name: &str, val: &SurfaceExpr) -> Option<usize> {
    let mut params: Vec<&str> = Vec::new();
    let mut body = val;
    while let SurfaceExpr::Lambda(_, binders, inner) = body {
        for b in binders {
            params.push(&b.name);
        }
        body = inner;
    }

    if params.is_empty() {
        return None;
    }

    find_match_on_param(body, &params, func_name)
}

/// Search for a `match` expression that scrutinizes one of the parameters
/// and contains recursive calls with sub-patterns.
fn find_match_on_param(body: &SurfaceExpr, params: &[&str], func_name: &str) -> Option<usize> {
    stack_safe(|| match body {
        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            if let SurfaceExpr::Ident(_, scrut_name) = scrutinee.as_ref() {
                if let Some(pos) = params.iter().position(|p| p == scrut_name) {
                    let has_rec = arms
                        .iter()
                        .any(|arm| contains_self_reference(&arm.body, func_name));
                    if has_rec {
                        return Some(pos);
                    }
                }
            }
            None
        }
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            find_match_on_param(then_br, params, func_name)
                .or_else(|| find_match_on_param(else_br, params, func_name))
                .or_else(|| find_match_on_param(cond, params, func_name))
        }
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Let(_, _, _, inner) => {
            find_match_on_param(inner, params, func_name)
        }
        _ => None,
    })
}

/// Try to detect structural recursion from a type annotation.
fn detect_structural_from_type(ty: &SurfaceExpr) -> Option<usize> {
    let mut args: Vec<&SurfaceExpr> = Vec::new();
    let mut current = ty;
    loop {
        match current {
            SurfaceExpr::Arrow(_, from, to) => {
                args.push(from);
                current = to;
            }
            SurfaceExpr::Pi(_, binders, body) => {
                for b in binders {
                    if let Some(ref bt) = b.ty {
                        args.push(bt);
                    }
                }
                current = body;
            }
            _ => break,
        }
    }

    for (i, arg) in args.iter().enumerate() {
        if is_known_inductive_type(arg) {
            return Some(i);
        }
    }
    None
}

/// Check if a surface expression refers to a known inductive type.
fn is_known_inductive_type(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Ident(_, name) => matches!(
            name.as_str(),
            "Nat" | "Bool" | "List" | "Option" | "Fin" | "Vector" | "Array"
        ),
        SurfaceExpr::App(_, func, _) => is_known_inductive_type(func),
        SurfaceExpr::Paren(_, inner) => is_known_inductive_type(inner),
        _ => false,
    }
}

// =========================================================================
// Expression utilities
// =========================================================================

/// Replace all free-variable references to `old_fvar` with `new_fvar`.
pub(crate) fn replace_fvar(expr: &Expr, old_fvar: FVarId, new_fvar: FVarId) -> Expr {
    struct FVarReplacer {
        old: FVarId,
        new: FVarId,
    }
    impl ExprFolder for FVarReplacer {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.old {
                Expr::fvar(self.new)
            } else {
                Expr::fvar(id)
            }
        }
    }
    let mut folder = FVarReplacer {
        old: old_fvar,
        new: new_fvar,
    };
    folder.fold_expr(expr)
}

/// Count free-variable occurrences of `target` in an expression.
pub(crate) fn count_fvar_occurrences(expr: &Expr, target: FVarId) -> usize {
    struct Counter {
        target: FVarId,
        count: usize,
    }
    impl ExprFolder for Counter {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.target {
                self.count += 1;
            }
            Expr::fvar(id)
        }
    }
    let mut c = Counter { target, count: 0 };
    let _ = c.fold_expr(expr);
    c.count
}

/// Extract the parameter name at `position` from a lambda-wrapped surface expr.
pub(crate) fn extract_param_name(val: &SurfaceExpr, position: usize) -> Option<String> {
    let mut current = val;
    let mut idx = 0;
    loop {
        match current {
            SurfaceExpr::Lambda(_, binders, body) => {
                for b in binders {
                    if idx == position {
                        return Some(b.name.clone());
                    }
                    idx += 1;
                }
                current = body;
            }
            _ => return None,
        }
    }
}

/// Count the number of leading lambda parameters in a surface expression.
pub(crate) fn count_lambda_params(val: &SurfaceExpr) -> usize {
    let mut count = 0;
    let mut current = val;
    loop {
        match current {
            SurfaceExpr::Lambda(_, binders, body) => {
                count += binders.len();
                current = body;
            }
            _ => return count,
        }
    }
}

/// Collect all names in a mutual let-rec block that reference each other.
pub(crate) fn find_mutual_references(bindings: &[(String, &SurfaceExpr)]) -> Vec<Vec<usize>> {
    let n = bindings.len();
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, (_, val)) in bindings.iter().enumerate() {
        for (j, (name, _)) in bindings.iter().enumerate() {
            if contains_self_reference(val, name) {
                deps[i].push(j);
            }
        }
    }
    deps
}
