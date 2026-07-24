// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

pub(super) fn mk_rel(rel_name: &str, ty_name: &str, inst_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(rel_name), vec![Level::zero()]),
                    Expr::const_(Name::from_string(ty_name), vec![]),
                ),
                Expr::const_(Name::from_string(inst_name), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn make_int_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LE.le", "Int", "instLEInt", lhs, rhs)
}

pub(super) fn make_real_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LE.le", "Real", "instLEReal", lhs, rhs)
}

pub(super) fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name == &Name::from_string(needle),
        ExprKind::App(f, a) => expr_contains_const(f, needle) || expr_contains_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, needle)
        }
        _ => false,
    }
}
