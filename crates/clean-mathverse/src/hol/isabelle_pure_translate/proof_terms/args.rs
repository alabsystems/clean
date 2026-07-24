// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx` spine proof-argument helpers: `apply_proof_args`, `proof_args`,
//! `first_proof_arg`, and `first_proof_arg_expecting`. Split out of the original
//! `proof_terms` module verbatim.

use super::super::super::isabelle_pure::IsaTerm;
use super::super::*;
use super::*;
use clean_kernel::Expr;

impl Ctx {
    /// Apply a spine's proof-typed arguments to a base proof term (left to
    /// right). Term args are ignored here (they were already consumed building
    /// `base`). Used for axioms built in closed `fun premises => …` form so the
    /// bare and applied occurrences are handled uniformly.
    pub(crate) fn apply_proof_args(
        &mut self,
        base: Expr,
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        let mut e = base;
        for arg in spine {
            if let SpineArg::Proof(p) = arg {
                e = Expr::app(e, self.translate_proof(p, closure, binders)?);
            }
        }
        Ok(e)
    }

    /// Translate every proof-typed argument on a spine (in order).
    pub(crate) fn proof_args(
        &mut self,
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Vec<Expr>, TranslateError> {
        let mut out = Vec::new();
        for arg in spine {
            if let SpineArg::Proof(p) = arg {
                out.push(self.translate_proof(p, closure, binders)?);
            }
        }
        Ok(out)
    }

    /// Translate the first proof-typed argument on a spine.
    pub(crate) fn first_proof_arg(
        &mut self,
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        self.proof_args(spine, closure, binders)?
            .into_iter()
            .next()
            .ok_or(TranslateError::Unsupported("expected a proof argument"))
    }

    /// Translate the first proof-typed argument on a spine **with its expected
    /// equation sides** `(a, b)` known (it proves `a ≡ b`), routing it through the
    /// [`Self::translate_eq_expecting`] channel. Returns `Ok(None)` when that
    /// channel does not handle the sub-proof (e.g. it is not an equation axiom with
    /// known operands), so the caller falls back to the plain
    /// [`Self::first_proof_arg`]. Used by the `Pure.symmetric` arm to discharge a
    /// bare `…_dict` axiom (no exported statement) reflexively against the sides the
    /// enclosing `symmetric` spine supplies.
    pub(crate) fn first_proof_arg_expecting(
        &mut self,
        spine: &[SpineArg],
        a: &IsaTerm,
        b: &IsaTerm,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(pr) = proof_spine_args(spine).into_iter().next() else {
            return Ok(None);
        };
        self.translate_eq_expecting(pr, a, b, closure, binders)
    }
}
