// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind};

pub(super) fn strip_trigger_wrappers(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) =
        current.kind()
    {
        current = inner;
    }
    current
}

/// Normalize transparent wrappers recursively so wrapped and unwrapped trigger
/// variants compare equal and deduplicate correctly.
pub(super) fn deep_strip_wrappers(expr: &Expr) -> Expr {
    crate::bridge::stack_safe(|| {
        let stripped = strip_trigger_wrappers(expr);
        match stripped.kind() {
            ExprKind::App(f, a) => Expr::app(deep_strip_wrappers(f), deep_strip_wrappers(a)),
            ExprKind::Lam(bd, ty, body) => {
                Expr::lam(*bd, deep_strip_wrappers(ty), deep_strip_wrappers(body))
            }
            ExprKind::Pi(bd, ty, body) => {
                Expr::pi(*bd, deep_strip_wrappers(ty), deep_strip_wrappers(body))
            }
            ExprKind::Let(name, ty, val, body, mono) => Expr::let_named(
                name.clone(),
                deep_strip_wrappers(ty),
                deep_strip_wrappers(val),
                deep_strip_wrappers(body),
                *mono,
            ),
            _ => stripped.clone(),
        }
    })
}

pub(super) fn collect_trigger_app_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = strip_trigger_wrappers(expr);
    while let ExprKind::App(func, arg) = current.kind() {
        args.push(arg.as_ref());
        current = strip_trigger_wrappers(func);
    }
    args.reverse();
    (current, args)
}
