// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry recognizers on expressions.

use std::sync::LazyLock;

use super::{Expr, ExprKind, ZFCSetExpr};
use crate::name::Name;

/// Pre-interned names for sorry recognizers (avoids repeated allocation in tree walks).
static SORRY: LazyLock<Name> = LazyLock::new(|| Name::from_string("sorry"));
static SORRY_AX: LazyLock<Name> = LazyLock::new(|| Name::from_string("sorryAx"));
static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
static TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("true"));

#[derive(Clone, Copy, Default)]
struct SorryFlags {
    has_sorry: bool,
    has_explicit: bool,
    has_synthetic: bool,
}

impl SorryFlags {
    fn observe_occurrence(&mut self, occurrence: &Expr) {
        self.has_sorry = true;
        if occurrence.is_synthetic_sorry() {
            self.has_synthetic = true;
        } else {
            self.has_explicit = true;
        }
    }

    fn all_set(&self) -> bool {
        self.has_sorry && self.has_explicit && self.has_synthetic
    }
}

fn is_true_name(name: &Name) -> bool {
    *name == *BOOL_TRUE || *name == *TRUE
}

/// Whether `name` is one of the two sorry constants (`sorry`, `sorryAx`).
///
/// THE SOUNDNESS-RELEVANT QUESTION IS ONLY THIS: does the constant occur. Any
/// occurrence of `sorryAx` — whatever its arguments, fully applied, partially
/// applied, eta-expanded, under a binder, as an argument to something else —
/// is an appeal to the axiom `sorryAx : {α : Sort u} → Bool → α`, and so to a
/// proof of anything. The Bool flag is PROVENANCE ONLY (Lean's
/// `synthetic := true` marks an elaborator-inserted sorry); it has no logical
/// content. Until 2026-09-28 the recognizers here matched `sorryAx` only as
/// `@sorryAx α b` with `b` literally `true`/`false`, so
/// `theorem bad : False := @sorryAx False (!true)` — and `sorryAx False`
/// partially applied — passed `clean check` with `sorry_axioms: 0`.
fn is_sorry_const_name(name: &Name) -> bool {
    *name == *SORRY || *name == *SORRY_AX
}

/// The head constant of `expr`'s application spine, when it is a sorry
/// constant.
fn sorry_head(expr: &Expr) -> Option<&Name> {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) if is_sorry_const_name(name) => Some(name),
        _ => None,
    }
}

/// The literal provenance flag of a `sorryAx` application: `Some(arg)` when
/// the spine is `sorryAx α flag …` (the flag is the SECOND argument; a `sorryAx`
/// at a function type may carry more). Provenance only — see
/// [`is_sorry_const_name`].
fn synthetic_flag_arg(expr: &Expr) -> Option<&Expr> {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) if *name == *SORRY_AX => {
            let args = expr.get_app_args();
            args.get(1).copied()
        }
        _ => None,
    }
}

/// Push the children of `curr` for a sorry scan, treating a sorry-headed
/// application spine as ONE occurrence: only its arguments are scanned (a
/// sorry can hide in an argument), never its partial-application prefixes,
/// which would each be counted again as a separate, flag-less occurrence.
///
/// Returns the occurrence when `curr` is one.
pub(super) fn push_sorry_scan_children<'a>(
    stack: &mut Vec<&'a Expr>,
    curr: &'a Expr,
) -> Option<&'a Expr> {
    if sorry_head(curr).is_some() {
        stack.extend(curr.get_app_args_iter());
        return Some(curr);
    }
    push_expr_children(stack, curr);
    None
}

fn push_zfc_set_children<'a>(stack: &mut Vec<&'a Expr>, set_expr: &'a ZFCSetExpr) {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(a)
        | ZFCSetExpr::Union(a)
        | ZFCSetExpr::PowerSet(a)
        | ZFCSetExpr::Choice(a) => stack.push(a),
        ZFCSetExpr::Pair(a, b)
        | ZFCSetExpr::Separation { set: a, pred: b }
        | ZFCSetExpr::Replacement { set: a, func: b } => {
            stack.push(b);
            stack.push(a);
        }
    }
}

pub(super) fn push_expr_children<'a>(stack: &mut Vec<&'a Expr>, curr: &'a Expr) {
    match curr.kind() {
        ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
        ExprKind::App(f, a) => {
            stack.push(a);
            stack.push(f);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack.push(body);
            stack.push(ty);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack.push(body);
            stack.push(val);
            stack.push(ty);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            stack.push(inner);
        }
        ExprKind::CubicalPath { ty, left, right } => {
            stack.push(right);
            stack.push(left);
            stack.push(ty);
        }
        ExprKind::CubicalPathLam { body } => stack.push(body),
        ExprKind::CubicalPathApp { path, arg } => {
            stack.push(arg);
            stack.push(path);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            stack.push(base);
            stack.push(u);
            stack.push(phi);
            stack.push(ty);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            stack.push(base);
            stack.push(phi);
            stack.push(ty);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            stack.push(base);
            stack.push(s);
            stack.push(r);
            stack.push(ty);
        }
        ExprKind::ZFCSet(set_expr) => push_zfc_set_children(stack, set_expr),
        ExprKind::ZFCMem { element, set } => {
            stack.push(set);
            stack.push(element);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            stack.push(pred);
            stack.push(domain);
        }
    }
}

impl Expr {
    /// Whether this expression is a sorry occurrence: its application head is
    /// the constant `sorry` or `sorryAx`, with ANY arguments (none, some, a
    /// non-literal flag, more than two).
    pub fn is_sorry(&self) -> bool {
        sorry_head(self).is_some()
    }

    /// Whether this expression is a synthetic/internal sorry: a `sorryAx`
    /// application whose provenance flag is LITERALLY `true`.
    ///
    /// Provenance for messages only. Never decide soundness with it: a sorry
    /// that is not synthetic is still a sorry ([`Expr::is_non_synthetic_sorry`]).
    pub fn is_synthetic_sorry(&self) -> bool {
        synthetic_flag_arg(self).is_some_and(|arg| match arg.kind() {
            ExprKind::Const(name, _) => is_true_name(name),
            _ => false,
        })
    }

    /// Whether this expression is a sorry occurrence that is NOT a literal
    /// synthetic one: the legacy `sorry` constant, `sorryAx` with the literal
    /// flag `false`, and every `sorryAx` whose flag is missing or not a literal
    /// (`!true`, `decide False`, a variable, …). Each of those is user-written
    /// in effect — the elaborator only ever mints the literal forms.
    pub fn is_non_synthetic_sorry(&self) -> bool {
        self.is_sorry() && !self.is_synthetic_sorry()
    }

    /// Whether the expression tree contains any sorry occurrence.
    pub fn has_sorry(&self) -> bool {
        self.collect_sorry_flags().has_sorry
    }

    /// Whether the expression tree contains any synthetic sorry term.
    pub fn has_synthetic_sorry(&self) -> bool {
        self.collect_sorry_flags().has_synthetic
    }

    /// Whether the expression tree contains any explicit/non-synthetic sorry term.
    pub fn has_non_synthetic_sorry(&self) -> bool {
        self.collect_sorry_flags().has_explicit
    }

    /// The number of sorry occurrences in the expression tree, each maximal
    /// application spine counted once (`@sorryAx α true` is ONE occurrence,
    /// not two), a bare `sorryAx` / `sorry` constant counted as one.
    pub fn count_sorry_occurrences(&self) -> usize {
        let mut count = 0usize;
        let mut stack = vec![self];
        while let Some(curr) = stack.pop() {
            if push_sorry_scan_children(&mut stack, curr).is_some() {
                count = count.saturating_add(1);
            }
        }
        count
    }

    fn collect_sorry_flags(&self) -> SorryFlags {
        let mut flags = SorryFlags::default();
        let mut stack = vec![self];
        while let Some(curr) = stack.pop() {
            if let Some(occurrence) = push_sorry_scan_children(&mut stack, curr) {
                flags.observe_occurrence(occurrence);
                if flags.all_set() {
                    break;
                }
            }
        }
        flags
    }

    /// Scan the expression tree for sorry terms, returning all provenance
    /// flags in a single pass.
    ///
    /// Returns `(has_sorry, has_explicit, has_synthetic)`. This is more
    /// efficient than calling `has_sorry()`, `has_non_synthetic_sorry()`, and
    /// `has_synthetic_sorry()` individually, which each perform a separate
    /// full tree walk.
    pub fn sorry_scan(&self) -> (bool, bool, bool) {
        let flags = self.collect_sorry_flags();
        (flags.has_sorry, flags.has_explicit, flags.has_synthetic)
    }
}

#[cfg(test)]
#[path = "sorry_occurrence_tests.rs"]
mod sorry_occurrence_tests;
