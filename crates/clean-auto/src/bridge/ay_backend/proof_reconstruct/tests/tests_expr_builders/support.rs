// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Expr, ExprKind};

/// Walk an Expr tree checking for an ExprKind::Const with the given name.
pub(super) fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) if name.to_string() == target => {
            return true;
        }
        ExprKind::App(f, a)
            if (expr_contains_const(f, target) || expr_contains_const(a, target)) =>
        {
            return true;
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body)
            if (expr_contains_const(ty, target) || expr_contains_const(body, target)) =>
        {
            return true;
        }
        _ => {}
    }
    false
}
