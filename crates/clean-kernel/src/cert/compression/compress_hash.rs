// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-recursive helpers for certificate compression.

use crate::expr::{Expr, ExprKind};

/// Get a descriptive name for an expression kind.
pub(crate) fn expr_name(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::BVar(_) => "BVar",
        ExprKind::FVar(_) => "FVar",
        ExprKind::Sort(_) => "Sort",
        ExprKind::Const(_, _) => "Const",
        ExprKind::App(_, _) => "App",
        ExprKind::Lam(_, _, _) => "Lam",
        ExprKind::Pi(_, _, _) => "Pi",
        ExprKind::Let(_, _, _, _, _) => "Let",
        ExprKind::Lit(_) => "Lit",
        ExprKind::Proj(_, _, _) => "Proj",
        ExprKind::MData(_, _) => "MData",
        ExprKind::CubicalInterval => "CubicalInterval",
        ExprKind::CubicalI0 => "CubicalI0",
        ExprKind::CubicalI1 => "CubicalI1",
        ExprKind::CubicalPath { .. } => "CubicalPath",
        ExprKind::CubicalPathLam { .. } => "CubicalPathLam",
        ExprKind::CubicalPathApp { .. } => "CubicalPathApp",
        ExprKind::CubicalHComp { .. } => "CubicalHComp",
        ExprKind::CubicalTransp { .. } => "CubicalTransp",
        ExprKind::CubicalCoe { .. } => "CubicalCoe",
        ExprKind::ZFCSet(_) => "ZFCSet",
        ExprKind::ZFCMem { .. } => "ZFCMem",
        ExprKind::ZFCComprehension { .. } => "ZFCComprehension",
        ExprKind::SProp => "SProp",
        ExprKind::Squash(_) => "Squash",
    }
    .to_string()
}
