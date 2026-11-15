// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small expression and level helpers for `inhabited_nonempty.rs`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolderOpt, FVarId, Level, LevelVec};

/// `Const(name, _) ↦ FVar(fvar)`.
pub(super) struct ConstToFVar<'a> {
    pub(super) name: &'a Name,
    pub(super) fvar: FVarId,
}

impl ExprFolderOpt for ConstToFVar<'_> {
    fn fold_const_opt(&mut self, name: &Name, _levels: &LevelVec) -> Option<Expr> {
        (name == self.name).then(|| Expr::fvar(self.fvar))
    }
}

/// `FVar(fvar) ↦ replacement`.
pub(super) struct FVarToExpr<'a> {
    pub(super) fvar: FVarId,
    pub(super) replacement: &'a Expr,
}

impl ExprFolderOpt for FVarToExpr<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_fvar_quick()
    }

    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        (id == self.fvar).then(|| self.replacement.clone())
    }
}

pub(super) fn mentions_fvar(expr: &Expr, id: FVarId) -> bool {
    expr.abstract_fvar(id) != *expr
}

/// Lean's `decLevel?` succeeds (`Meta/DecLevel`: `succ u ↦ u`, `max` /
/// `imax` when both sides decrement, `zero` / a parameter never).
pub(super) fn decrements(level: &Level) -> bool {
    match level {
        Level::Succ(_) => true,
        Level::Max(a, b) | Level::IMax(a, b) => decrements(a) && decrements(b),
        _ => false,
    }
}
