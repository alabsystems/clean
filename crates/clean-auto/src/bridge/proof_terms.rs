// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Low-level proof term constructors for the SMT-Kernel Bridge.
//!
//! Builds individual Lean kernel proof terms (Eq.refl, Eq.symm, Eq.trans,
//! congr, congrArg) and provides type inference helpers (sort_level_of_type,
//! congr_universe_levels, get_type_for_term).
//!
//! All fallible methods return `BridgeResult<T>` with typed errors.

use clean_kernel::{Expr, ExprKind, Level};

use crate::smt::TermId;

use super::{BridgeError, BridgeResult, SmtBridge};

impl<'env> SmtBridge<'env> {
    /// Build `@congr.{u,v} α β f₁ f₂ a₁ a₂ hf ha`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn mk_congr(
        &self,
        u: Level,
        v: Level,
        alpha: &Expr,
        beta: &Expr,
        f1: &Expr,
        f2: &Expr,
        a1: &Expr,
        a2: &Expr,
        func_proof: &Expr,
        arg_proof: &Expr,
    ) -> Expr {
        super::eq_proof_builders::mk_congr(
            &u, &v, alpha, beta, f1, f2, a1, a2, func_proof, arg_proof,
        )
    }

    /// Build `@congrArg.{u,v} α β a₁ a₂ f h`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn mk_congr_arg(
        &self,
        u: Level,
        v: Level,
        alpha: &Expr,
        beta: &Expr,
        a1: &Expr,
        a2: &Expr,
        func: &Expr,
        arg_proof: &Expr,
    ) -> Expr {
        super::eq_proof_builders::mk_congr_arg(&u, &v, alpha, beta, a1, a2, func, arg_proof)
    }

    /// Get the type for a term.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::MissingTypeMapping` if no type is recorded for this term.
    pub(crate) fn get_type_for_term(&self, term: TermId) -> BridgeResult<Expr> {
        self.term_to_type
            .get(&term)
            .cloned()
            .ok_or(BridgeError::MissingTypeMapping(term))
    }

    /// Compute the sort level of `ty`. Given `ty : Sort u`, returns `u`.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` if `TypeChecker::infer_sort` fails.
    pub(crate) fn sort_level_of_type(&self, ty: &Expr) -> BridgeResult<Level> {
        let tc = self.make_tc();
        tc.infer_sort(ty).map_err(|e| BridgeError::InferSortFailed {
            context: format!("{e:?}"),
        })
    }

    /// Compute (u, v) for congrArg/congr: u = sort of α, v = sort of β for `f : α → β`.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::CongruenceInferFailed` if sort inference fails for
    /// either the argument type or the function's codomain.
    pub(crate) fn congr_universe_levels(
        &self,
        func_expr: &Expr,
        arg_ty: &Expr,
    ) -> BridgeResult<(Level, Level)> {
        let tc = self.make_tc();
        let u = tc
            .infer_sort(arg_ty)
            .map_err(|e| BridgeError::CongruenceInferFailed {
                context: format!("arg sort: {e:?}"),
            })?;
        let func_ty = tc
            .infer_type(func_expr)
            .map_err(|e| BridgeError::CongruenceInferFailed {
                context: format!("func type: {e:?}"),
            })?;
        let v = match func_ty.kind() {
            ExprKind::Pi(_, _, body) => {
                tc.infer_sort(body)
                    .map_err(|e| BridgeError::CongruenceInferFailed {
                        context: format!("codomain sort: {e:?}"),
                    })?
            }
            _ => {
                return Err(BridgeError::CongruenceInferFailed {
                    context: format!("expected Pi type for function, got {:?}", func_ty.kind()),
                });
            }
        };
        Ok((u, v))
    }

    /// Infer the codomain β from a function f : (x : α) → β.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::CongruenceInferFailed` if type inference fails
    /// or the function doesn't have a Pi type.
    pub(crate) fn infer_codomain(&self, func_expr: &Expr) -> BridgeResult<Expr> {
        let tc = self.make_tc();
        let func_ty = tc
            .infer_type(func_expr)
            .map_err(|e| BridgeError::CongruenceInferFailed {
                context: format!("func type for codomain: {e:?}"),
            })?;
        match func_ty.kind() {
            ExprKind::Pi(_, _, body) => Ok(body.as_ref().clone()),
            _ => Err(BridgeError::CongruenceInferFailed {
                context: format!("expected Pi for codomain, got {:?}", func_ty.kind()),
            }),
        }
    }

    /// Build `@Eq.refl.{u} α a`.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` if the sort of `ty` cannot be computed.
    pub(crate) fn mk_eq_refl(&self, ty: &Expr, val: &Expr) -> BridgeResult<Expr> {
        let u = self.sort_level_of_type(ty)?;
        Ok(super::eq_proof_builders::mk_eq_refl(&u, ty, val))
    }

    /// Build `@Eq.symm.{u} α a b h`.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` if the sort of `eq_ty` cannot be computed.
    pub(crate) fn mk_eq_symm(
        &self,
        eq_ty: &Expr,
        a: &Expr,
        b: &Expr,
        proof: &Expr,
    ) -> BridgeResult<Expr> {
        let u = self.sort_level_of_type(eq_ty)?;
        Ok(super::eq_proof_builders::mk_eq_symm(&u, eq_ty, a, b, proof))
    }

    /// Build `@Eq.trans.{u} α a b c h₁ h₂`.
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` if the sort of `eq_ty` cannot be computed.
    pub(crate) fn mk_eq_trans(
        &self,
        eq_ty: &Expr,
        a: &Expr,
        b: &Expr,
        c: &Expr,
        p1: &Expr,
        p2: &Expr,
    ) -> BridgeResult<Expr> {
        let u = self.sort_level_of_type(eq_ty)?;
        Ok(super::eq_proof_builders::mk_eq_trans(
            &u, eq_ty, a, b, c, p1, p2,
        ))
    }
}
