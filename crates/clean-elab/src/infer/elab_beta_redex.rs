// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A fully applied lambda with untyped binders, `(fun x₁ … xₙ => b) a₁ … aₙ`,
//! elaborated in Lean's order (`Lean/Elab/App.lean` `elabAppArgs`): the head
//! first, so each binder's type is a metavariable the body may pin, then each
//! argument against its binder's type, coerced where its own type differs.
//! The β-redex is kept as written, so every argument, recursive calls
//! included, stays in the term.
//!
//! The caller (`elaborate_surface_inner`'s β-redex rewrite) uses this only
//! once the let-chain form of the same redex is known to elaborate; see the
//! comment there for why the two orders differ.

use super::*;

impl ElabCtx<'_> {
    pub(super) fn elab_beta_redex_lean_order(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        let expected = self.current_expected_type.clone();
        // A retry with the binder types the first attempt settled
        // (`pinned_redex_binder_types`, below) types the head's binders.
        let pinned = self.take_pinned_redex_binder_types(func);
        self.pinned_lambda_binder_types = pinned;
        let head = self.elaborate_with_expected_type(func, None);
        let unconsumed = !std::mem::take(&mut self.pinned_lambda_binder_types).is_empty();
        let mut applied = head?;
        if unconsumed {
            return Err(ElabError::CannotInfer);
        }
        let mut func_ty = self.infer_type(&applied)?;
        let mut domains: Vec<Expr> = Vec::with_capacity(args.len());
        // `elabAppArgs` runs `propagateExpectedType` before each explicit
        // argument: a result type that does not depend on the remaining
        // arguments meets the expected type first, so `(fun z => z)
        // (Nat.succ 0 - 7) : Int` elaborates its argument at `Int` (`-6` in
        // Lean 4.8.0; `0` when the argument came first). Taken only where it
        // can inform an argument, a result type that shares a metavariable
        // with a remaining argument's binder type; any other result meets the
        // expected type after the arguments, below, as it did before (pinning
        // an operator's result early, `(fun a b => a * b + 1) (…) 4 = 29`,
        // left a carrier Clean's drain could no longer settle).
        let mut propagate = true;
        for (index, arg) in args.iter().enumerate() {
            if propagate && self.redex_result_reaches_a_domain(&func_ty, args.len() - index) {
                propagate = self.propagate_expected_type(&func_ty, &args[index..]);
            }
            let func_ty_whnf = self.whnf(&self.metas.instantiate(&func_ty));
            let ExprKind::Pi(_, domain, codomain) = func_ty_whnf.kind() else {
                return Err(ElabError::TooManyArguments {
                    func_type: format!("{func_ty_whnf}"),
                    remaining_args: 1,
                });
            };
            let domain = self.metas.instantiate(domain);
            domains.push(domain.clone());
            let value = self.elaborate_with_expected_type(&arg.expr, Some(domain.clone()))?;
            let value_ty = self.infer_type(&value)?;
            let value = if self.try_unify(&value_ty, &domain) {
                value
            } else {
                self.try_coerce(&value, &value_ty, &domain).ok_or_else(|| {
                    ElabError::TypeMismatch {
                        expected: format!("{}", self.metas.instantiate(&domain)),
                        actual: format!("{}", self.metas.instantiate(&value_ty)),
                    }
                })?
            };
            func_ty = codomain.instantiate(&value);
            applied = Expr::app(applied, value);
        }
        if let Some(expected) = expected {
            // As `elabAppArgs` does: the result type meets the expected type
            // before the postponed instance goals are drained. A mismatch
            // (Clean's binop defaulted a carrier the expected type would
            // have pinned, `(fun k => -k + 0) 5 : Int`) fails this order, and
            // the caller keeps the let-chain's term.
            //
            // One mismatch is Lean's own: a result type the head and the
            // arguments made GROUND, under a ground expected type. Lean
            // elaborated the head with no expected type (`elabAppFn`), so the
            // body's type was settled before the expected type was seen, and
            // `ensureHasType` coerces the whole application:
            // `((fun y => y - (7 : Nat)) 1 : Int)` is `↑((fun y => y - 7) 1)`,
            // `0` in Lean 4.8.0. The let-chain's term instead elaborated the
            // body against `Int` (`↑1 - ↑7 = -6`), and `≠ 0` was accepted. So
            // that mismatch coerces here, and the let-chain is not consulted.
            let result_ty = self.metas.instantiate(&func_ty);
            let expected = self.metas.instantiate(&expected);
            if !self.try_unify(&result_ty, &expected) {
                let result_ty = self.metas.instantiate(&result_ty);
                let expected = self.metas.instantiate(&expected);
                let ground = !self.has_metavars(&result_ty) && !self.has_metavars(&expected);
                let coerced = if ground {
                    let applied = self.metas.instantiate(&applied);
                    self.try_coerce(&applied, &result_ty, &expected)
                } else {
                    None
                };
                let Some(coerced) = coerced else {
                    return Err(ElabError::TypeMismatch {
                        expected: format!("{expected}"),
                        actual: format!("{result_ty}"),
                    });
                };
                applied = coerced;
            }
        }
        self.retry_postponed_open_carrier_instances();
        let applied = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&applied));
        self.redex_binder_domains = Some((func.span(), domains));
        // Clean abstracts a binder before the instance goals its body queued
        // are answered, so an answer over the binder (`Decidable (y = 1)`,
        // `instDecidableEqNat y 1` once the argument made `y : Nat`) escapes
        // it; the declaration would then be refused as holding a free
        // variable. The caller retries with the binder types this attempt
        // settled (`retry_redex_with_settled_binders`).
        if self.mentions_escaped_local(&applied) {
            self.redex_binder_escaped = true;
            return Err(ElabError::CannotInfer);
        }
        Ok(applied)
    }

    /// The binder types a failed Lean-order attempt of the β-redex headed by
    /// `func` settled, when that attempt failed only because an instance
    /// answer escaped a binder (`redex_binder_escaped`) and every type is
    /// ground; read inside the attempt, before its rollback.
    pub(super) fn settled_redex_binder_types(&mut self, func: &SurfaceExpr) -> Option<Vec<Expr>> {
        let escaped = std::mem::take(&mut self.redex_binder_escaped);
        let (span, domains) = self.redex_binder_domains.take()?;
        if !escaped || span != func.span() {
            return None;
        }
        let types: Vec<Expr> = domains
            .iter()
            .map(|d| self.metas.instantiate_levels(&self.metas.instantiate(d)))
            .collect();
        types
            .iter()
            .all(|t| !self.has_metavars(t) && !self.mentions_escaped_local(t))
            .then_some(types)
    }

    fn take_pinned_redex_binder_types(&mut self, func: &SurfaceExpr) -> Vec<Expr> {
        match self.pinned_redex_binder_types.take() {
            Some((span, types)) if span == func.span() => types,
            other => {
                self.pinned_redex_binder_types = other;
                Vec::new()
            }
        }
    }

    /// Whether `e` mentions a local (not a metavariable) that is not in the
    /// local context (`mentions_closed_local`, pruned by `has_fvar_quick`
    /// and DAG-aware).
    pub(super) fn mentions_escaped_local(&self, e: &Expr) -> bool {
        let mut visited: std::collections::HashSet<*const Expr> = std::collections::HashSet::new();
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            if !cur.has_fvar_quick() || !visited.insert(cur as *const Expr) {
                continue;
            }
            if let ExprKind::FVar(fvar) = cur.kind() {
                if MetaState::from_fvar(*fvar).is_none()
                    && !self.locals.iter().any(|(_, local, _)| local == fvar)
                {
                    return true;
                }
            }
            crate::unify::push_expr_children(cur, &mut stack);
        }
        false
    }

    /// Does the result type of `func_ty` after `remaining` binders, when it
    /// does not depend on them, share a metavariable with one of those
    /// binders' types?
    fn redex_result_reaches_a_domain(&self, func_ty: &Expr, remaining: usize) -> bool {
        let mut cur = self.metas.instantiate(func_ty);
        let mut domains = Vec::new();
        for _ in 0..remaining {
            let ExprKind::Pi(_, domain, body) = cur.kind() else {
                return false;
            };
            domains.push(domain.as_ref().clone());
            let next = body.as_ref().clone();
            cur = next;
        }
        if cur.has_loose_bvars() {
            return false;
        }
        let result_metas = self.collect_meta_fvars(&cur);
        !result_metas.is_empty()
            && domains
                .iter()
                .any(|d| !self.collect_meta_fvars(d).is_disjoint(&result_metas))
    }
}
