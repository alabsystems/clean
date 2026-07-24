// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Definitional equality for `CertVerifier`.
//!
//! Thin wrappers that delegate to the shared `CertExprEqContext` trait
//! defined in `expr_eq.rs`. The verifier supplies its own full WHNF
//! (beta, zeta, delta, projection, iota, quotient) via `reduction.rs`.
//!
//! Extracted per design `designs/2026-03-10-2485-cert-builder-equality-extraction-and-module-split.md`.

use crate::expr::Expr;
use crate::level::Level;

use super::expr_eq::CertExprEqContext;
use super::verifier::CertVerifier;

/// Implement the shared equality trait for CertVerifier.
/// The verifier provides full WHNF from `reduction.rs`.
impl<'env> CertExprEqContext for CertVerifier<'env> {
    fn whnf_for_eq(&self, e: &Expr) -> Expr {
        // Delegates to the verifier's full WHNF in reduction.rs
        self.whnf_impl(e)
    }
}

impl<'env> CertVerifier<'env> {
    /// Check definitional equality (stack-safe entry point).
    pub(super) fn def_eq(&self, a: &Expr, b: &Expr) -> bool {
        CertExprEqContext::def_eq_impl(self, a, b)
    }

    /// Structural equality after WHNF (stack-safe entry point, test-only).
    #[cfg(test)]
    pub(super) fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        CertExprEqContext::structural_eq_impl(self, a, b)
    }

    /// Level equality — normalizes both sides before comparison.
    pub(super) fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        CertExprEqContext::level_eq(self, l1, l2)
    }

    /// Internal def_eq_impl — delegates to the shared trait engine.
    /// Called extensively from `verifier.rs` for type checking.
    pub(super) fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        CertExprEqContext::def_eq_impl(self, a, b)
    }
}
