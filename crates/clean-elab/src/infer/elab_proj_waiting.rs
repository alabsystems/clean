// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A field-notation term whose receiver holds a numeral, `(1 - 7, 0).1` or
//! `(some (1 - 7)).getD 0`, elaborated against a ground expected type with the
//! receiver's numerals waiting, as Lean's are (`OfNat ?α n` pending until the
//! term is done): Lean elaborates the receiver with no expected type, resolves
//! the field from its head (`Prod`, `Option`), and the expected type then pins
//! the carrier, so `((1 - 7, 0).1 : Int)` is `-6` in Lean 4.8.0. Clean
//! defaulted the receiver's numerals to `Nat` first, and `((1 - 7, 0).1 :
//! Int) = 0 := by decide` was accepted.
//!
//! The same mechanism as a numeral `let` (R163, `elab_let_postpone.rs`): a
//! postponing scope, in a transaction; where the waiting order fails the eager
//! order stands, and a ground instance goal with no instance refuses.

use super::*;

impl ElabCtx<'_> {
    /// `Some` when `expr` is such a term and the waiting order decided it
    /// (its term, or a refusal Lean's typing makes); `None` to elaborate it in
    /// the eager order.
    pub(super) fn try_proj_with_waiting_numerals(
        &mut self,
        expr: &SurfaceExpr,
        expected: &Expr,
    ) -> Option<Result<Expr, ElabError>> {
        if self.postponing_let_depth > 0 || self.numeral_postpone_depth > 0 {
            return None;
        }
        let receiver = match Self::unwrap_surface_parens(expr) {
            SurfaceExpr::Proj(_, base, _) => base.as_ref(),
            SurfaceExpr::App(_, head, _) => match Self::unwrap_surface_parens(head) {
                SurfaceExpr::Proj(_, base, _) => base.as_ref(),
                _ => return None,
            },
            _ => return None,
        };
        if Self::surface_value_holds_numeral_pub(receiver) != Some(true) {
            return None;
        }
        let expected = self.metas.instantiate(expected);
        if self.has_metavars(&expected) || matches!(expected.kind(), ExprKind::Sort(_)) {
            return None;
        }
        self.lean_order_ground_refusal = None;
        let attempt = self.lean_order_attempt(|this| {
            this.with_postponing_let_scope(|this| {
                let term = this.elaborate_with_expected_type(expr, Some(expected.clone()))?;
                // The expected type meets the term's type before the scope
                // drains its numerals, as Lean's `ensureHasType` runs before
                // default instances apply.
                let ty = this.infer_type(&term)?;
                let _ = this.try_unify(&ty, &expected);
                Ok(term)
            })
        });
        match attempt {
            Ok(term) => Some(Ok(term)),
            Err(refusal @ ElabError::FailedToSynthesizeInstance { .. }) => Some(Err(refusal)),
            Err(_) => self.lean_order_ground_refusal.take().map(Err),
        }
    }
}
