// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reuse completed closed Nat reductions before comparing their suspended
//! argument spines. No new reduction, arithmetic rule, or cache authority.

use crate::{Expr, ExprKind, Literal};

use super::TypeChecker;

impl TypeChecker<'_> {
    fn cached_closed_nat(&self, expression: &Expr) -> Option<Expr> {
        if matches!(expression.kind(), ExprKind::Lit(Literal::Nat(_))) {
            return Some(expression.clone());
        }
        if expression.has_fvar_quick()
            || expression.has_expr_mvar_quick()
            || expression.has_level_mvar_quick()
            || expression.has_level_param_quick()
            || expression.loose_bvar_range() != 0
        {
            return None;
        }
        self.whnf_cache
            .borrow_mut()
            .get(expression)
            .filter(|normal| matches!(normal.kind(), ExprKind::Lit(Literal::Nat(_))))
    }

    pub(super) fn cached_nat_def_eq(&self, left: &Expr, right: &Expr) -> Option<bool> {
        // The semantic entry point has already established cache theory
        // custody. Only the ordinary full-WHNF cache is used: it records no
        // result from an exhausted reduction or a level-sharing refusal.
        // For these closed inputs, cached n and m establish left =def n and
        // right =def m in that same theory and configuration. Distinct Nat
        // literals are not convertible; identical literals are convertible.
        // Do not walk the original nested /256 spines again to rediscover it.
        let left = self.cached_closed_nat(left)?;
        let right = self.cached_closed_nat(right)?;
        Some(left == right)
    }
}
