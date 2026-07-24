// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared constants for the Eq declaration family.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Cached context holding shared names, sorts, and constants used across all Eq
/// initializer submodules. Created once by `init_eq` and passed by reference.
pub(crate) struct EqCtx {
    pub(crate) u: Name,
    pub(crate) sort_u: Expr,
    pub(crate) prop: Expr,
    pub(crate) eq_const: Expr,
    pub(crate) eq_refl_const: Expr,
}

impl EqCtx {
    pub(crate) fn new() -> Self {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]);
        let eq_refl_const =
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::param(u.clone())]);
        Self {
            u,
            sort_u,
            prop,
            eq_const,
            eq_refl_const,
        }
    }

    /// Build `@Eq.{u} α lhs rhs`
    pub(crate) fn eq(&self, alpha: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq_const.clone(), alpha.clone()), lhs),
            rhs,
        )
    }

    /// Build `@Eq.refl.{u} α value`
    pub(crate) fn refl(&self, alpha: &Expr, value: Expr) -> Expr {
        Expr::app(Expr::app(self.eq_refl_const.clone(), alpha.clone()), value)
    }
}
