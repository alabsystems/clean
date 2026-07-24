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
static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
static TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("true"));
static FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("false"));

#[derive(Clone, Copy, Default)]
struct SorryFlags {
    has_sorry: bool,
    has_explicit: bool,
    has_synthetic: bool,
}

impl SorryFlags {
    fn observe(&mut self, expr: &Expr) {
        self.has_sorry |= expr.is_sorry();
        self.has_explicit |= expr.is_non_synthetic_sorry();
        self.has_synthetic |= expr.is_synthetic_sorry();
    }

    fn all_set(&self) -> bool {
        self.has_sorry && self.has_explicit && self.has_synthetic
    }
}

fn is_true_name(name: &Name) -> bool {
    *name == *BOOL_TRUE || *name == *TRUE
}

fn is_false_name(name: &Name) -> bool {
    *name == *BOOL_FALSE || *name == *FALSE
}

fn synthetic_flag_arg(expr: &Expr) -> Option<&Expr> {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) if *name == *SORRY_AX => {
            let args = expr.get_app_args();
            if args.len() == 2 {
                Some(args[1])
            } else {
                None
            }
        }
        _ => None,
    }
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
    /// Whether this expression is a sorry-bearing term.
    pub fn is_sorry(&self) -> bool {
        if let ExprKind::Const(name, _) = self.get_app_fn().kind() {
            if *name == *SORRY {
                return true;
            }
        }
        synthetic_flag_arg(self).is_some()
    }

    /// Whether this expression is a synthetic/internal sorry term.
    pub fn is_synthetic_sorry(&self) -> bool {
        synthetic_flag_arg(self).is_some_and(|arg| match arg.kind() {
            ExprKind::Const(name, _) => is_true_name(name),
            _ => false,
        })
    }

    /// Whether this expression is an explicit/non-synthetic sorry term.
    pub fn is_non_synthetic_sorry(&self) -> bool {
        if let ExprKind::Const(name, _) = self.get_app_fn().kind() {
            if *name == *SORRY {
                return true;
            }
        }
        synthetic_flag_arg(self).is_some_and(|arg| match arg.kind() {
            ExprKind::Const(name, _) => is_false_name(name),
            _ => false,
        })
    }

    /// Whether the expression tree contains any sorry-bearing term.
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

    fn collect_sorry_flags(&self) -> SorryFlags {
        let mut flags = SorryFlags::default();
        let mut stack = vec![self];
        while let Some(curr) = stack.pop() {
            flags.observe(curr);
            if flags.all_set() {
                break;
            }
            push_expr_children(&mut stack, curr);
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
