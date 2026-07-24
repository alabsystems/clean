// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared constants for the HEq declaration family.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Cached context holding shared names, sorts, and constants used across all HEq
/// initializer submodules.
pub(crate) struct HeqCtx {
    pub(crate) u: Name,
    pub(crate) sort_u: Expr,
    pub(crate) prop: Expr,
    pub(crate) heq_const: Expr,
    pub(crate) heq_refl_const: Expr,
    pub(crate) eq_const: Expr,
}

impl HeqCtx {
    pub(crate) fn new() -> Self {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let heq_const = Expr::const_(Name::from_string("HEq"), vec![Level::param(u.clone())]);
        let heq_refl_const =
            Expr::const_(Name::from_string("HEq.refl"), vec![Level::param(u.clone())]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]);
        Self {
            u,
            sort_u,
            prop,
            heq_const,
            heq_refl_const,
            eq_const,
        }
    }

    /// Build `@HEq.{u} α a β b`
    pub(crate) fn heq(&self, alpha: &Expr, a: Expr, beta: &Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.heq_const.clone(), alpha.clone()), a),
                beta.clone(),
            ),
            b,
        )
    }

    /// Build `@Eq.{u} α lhs rhs`
    pub(crate) fn eq(&self, alpha: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq_const.clone(), alpha.clone()), lhs),
            rhs,
        )
    }
}
