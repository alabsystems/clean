// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builder-specific WHNF and thin equality wrappers.
//!
//! The builder's WHNF is intentionally simpler than the verifier's: it handles
//! beta, zeta, delta, and MData/Squash reductions only. Projection, iota, and
//! quotient reductions are not needed for builder-side type checking.

use std::sync::Arc;

use crate::env::TransparencyMode;
use crate::expr::{stack_safe, Expr, ExprKind};

use super::state::CertBuilder;

/// Implement the shared equality trait for CertBuilder.
/// The builder provides simplified WHNF (beta, zeta, delta, mdata/squash only).
impl<'env> super::super::expr_eq::CertExprEqContext for CertBuilder<'env> {
    fn whnf_for_eq(&self, e: &Expr) -> Expr {
        self.whnf(e)
    }
}

impl<'env> CertBuilder<'env> {
    // Equality methods delegate to the shared CertExprEqContext trait in expr_eq.rs.
    // This eliminates ~330 lines of duplicated equality logic between builder and verifier.

    pub(crate) fn def_eq(&self, a: &Expr, b: &Expr) -> bool {
        use super::super::expr_eq::CertExprEqContext;
        // The builder keeps the trait's type-directed hook at its disabled
        // default (fail-closed), so the equality binder context is never
        // consulted — an empty seed is correct.
        CertExprEqContext::def_eq_impl(self, &mut Vec::new(), a, b)
    }

    #[cfg(test)]
    pub(crate) fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        use super::super::expr_eq::CertExprEqContext;
        CertExprEqContext::structural_eq_impl(self, a, b)
    }

    pub(super) fn whnf(&self, e: &Expr) -> Expr {
        if let Some(cache) = &self.whnf_cache {
            if let Some(whnf) = cache.get(e) {
                return whnf;
            }
        }

        let whnf = stack_safe(|| self.whnf_impl(e));

        if let Some(cache) = &self.whnf_cache {
            cache.insert(e.clone(), whnf.clone());
        }

        whnf
    }

    fn whnf_impl(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                // Native Nat literal reduction (Lean 4 `reduce_nat` parity):
                // closed `Nat.succ`/`Nat.add`/…/`Nat.ble` collapse to a literal
                // so the builder's emitted cert agrees with the verifier's
                // Nat-aware WHNF. See `cert/nat_reduce.rs`.
                if let ExprKind::Const(_, _) = e.get_app_fn().kind {
                    if let Some(reduced) =
                        super::super::nat_reduce::reduce_nat(e, &|x| self.whnf_impl(x))
                    {
                        return self.whnf_impl(&reduced);
                    }
                }
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone())),
                }
            }
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            ExprKind::Const(name, levels) => self
                .env
                .unfold_with_transparency(name, levels, TransparencyMode::Default)
                .map_or_else(|| e.clone(), |val| self.whnf_impl(&val)),
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }
}
