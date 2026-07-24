// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay::{Sort, Term};
use ay_translate::{ops, TermTranslator, TranslationTermHost};
use clean_kernel::{Expr, FVarId};

use super::super::{infer_sort_from_lean_type, reject_unsound_domain_ty, AyError, AyResult};
use super::LeanExprTranslator;
use crate::bridge::expr_classifier::LogicalForm;

impl LeanExprTranslator {
    /// Translate a classified logical form to a ay term.
    pub(super) fn translate_classified<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        form: LogicalForm,
    ) -> AyResult<Term> {
        match form {
            LogicalForm::And(a, b) => {
                let a = TermTranslator::translate(self, ctx, &a)?;
                let b = TermTranslator::translate(self, ctx, &b)?;
                Ok(ops::bool_nary(ctx, ops::NaryBoolOp::And, &[a, b]))
            }
            LogicalForm::Or(a, b) => {
                let a = TermTranslator::translate(self, ctx, &a)?;
                let b = TermTranslator::translate(self, ctx, &b)?;
                Ok(ops::bool_nary(ctx, ops::NaryBoolOp::Or, &[a, b]))
            }
            LogicalForm::Not(a) => {
                let a = TermTranslator::translate(self, ctx, &a)?;
                Ok(ops::bool_not(ctx, a))
            }
            LogicalForm::Eq { lhs, rhs, .. } => {
                let lhs = TermTranslator::translate(self, ctx, &lhs)?;
                let rhs = TermTranslator::translate(self, ctx, &rhs)?;
                Ok(ops::compare(ctx, ops::Comparison::Eq, lhs, rhs))
            }
            LogicalForm::Neq { lhs, rhs, .. } => {
                let lhs = TermTranslator::translate(self, ctx, &lhs)?;
                let rhs = TermTranslator::translate(self, ctx, &rhs)?;
                Ok(ops::compare(ctx, ops::Comparison::Ne, lhs, rhs))
            }
            LogicalForm::Iff(a, b) => {
                let a = TermTranslator::translate(self, ctx, &a)?;
                let b = TermTranslator::translate(self, ctx, &b)?;
                let forward = ops::implies(ctx, a, b);
                let backward = ops::implies(ctx, b, a);
                Ok(ops::bool_nary(
                    ctx,
                    ops::NaryBoolOp::And,
                    &[forward, backward],
                ))
            }
            LogicalForm::Implies(a, b) => {
                let a = TermTranslator::translate(self, ctx, &a)?;
                let b = TermTranslator::translate(self, ctx, &b)?;
                Ok(ops::implies(ctx, a, b))
            }
            LogicalForm::True => Ok(ctx.solver().bool_const(true)),
            LogicalForm::False => Ok(ctx.solver().bool_const(false)),
            LogicalForm::Lt { ty, lhs, rhs, .. } => {
                self.translate_comparison(ctx, &ty, &lhs, &rhs, ops::Comparison::Lt)
            }
            LogicalForm::Le { ty, lhs, rhs, .. } => {
                self.translate_comparison(ctx, &ty, &lhs, &rhs, ops::Comparison::Le)
            }
            LogicalForm::Gt { ty, lhs, rhs, .. } => {
                self.translate_comparison(ctx, &ty, &lhs, &rhs, ops::Comparison::Gt)
            }
            LogicalForm::Ge { ty, lhs, rhs, .. } => {
                self.translate_comparison(ctx, &ty, &lhs, &rhs, ops::Comparison::Ge)
            }
            LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. } => self.translate_arithmetic_form(ctx, form),
            LogicalForm::Exists { binder_type, body } => {
                self.translate_exists_skolemize(ctx, &binder_type, &body)
            }
            LogicalForm::Forall { .. } => Err(AyError::UnsupportedExpr(
                "universal quantifier not directly supported in AyBackend translation".to_string(),
            )),
            LogicalForm::Atom(_) => {
                unreachable!("Atom handled by caller before translate_classified")
            }
        }
    }

    /// Translate a comparison with defense-in-depth domain check (#2852).
    fn translate_comparison<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        cmp: ops::Comparison,
    ) -> AyResult<Term> {
        reject_unsound_domain_ty(ty)?;
        let lhs = TermTranslator::translate(self, ctx, lhs)?;
        let rhs = TermTranslator::translate(self, ctx, rhs)?;
        Ok(ops::compare(ctx, cmp, lhs, rhs))
    }

    /// Allocate a collision-safe FVar placeholder for an existential witness
    /// and bind it to a ay skolem term. Part of #2848.
    fn alloc_skolem_fvar<H: TranslationTermHost<FVarId>>(&self, ctx: &mut H, sort: Sort) -> Expr {
        let mut state = self.state.borrow_mut();
        let skolem_name = format!("sk_exists_{}", state.next_skolem_id);
        state.next_skolem_id += 1;
        let placeholder_id = FVarId::new(state.next_internal_fvar);
        state.next_internal_fvar += 1;
        drop(state);
        assert!(
            !placeholder_id.is_sentinel(),
            "skolem FVar in sentinel range"
        );
        let skolem_term = ctx.fresh_const(&skolem_name, sort);
        let expr = Expr::fvar(placeholder_id);
        self.state
            .borrow_mut()
            .expr_to_term
            .insert(expr.clone(), skolem_term);
        expr
    }

    /// Skolemize an existential: exists x. P(x) -> P(sk).
    fn translate_exists_skolemize<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        binder_type: &Expr,
        body: &Expr,
    ) -> AyResult<Term> {
        let sort = infer_sort_from_lean_type(binder_type)?;
        let skolem_expr = self.alloc_skolem_fvar(ctx, sort);
        TermTranslator::translate(self, ctx, &body.instantiate(&skolem_expr))
    }

    /// Translate the non-lambda `Exists` fallback in atom application lowering.
    pub(super) fn translate_exists_const_fallback<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        binder_type: &Expr,
        body_fn: &Expr,
    ) -> AyResult<Term> {
        let sort = infer_sort_from_lean_type(binder_type)?;
        let skolem_expr = self.alloc_skolem_fvar(ctx, sort);
        let applied = Expr::app(body_fn.clone(), skolem_expr);
        TermTranslator::translate(self, ctx, &applied)
    }
}
