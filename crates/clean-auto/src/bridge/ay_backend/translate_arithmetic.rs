// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic translation with type-specific Nat semantics.
//!
//! Nat operations have total/monus semantics:
//! - `Nat.sub a b = max(a - b, 0)` (monus)
//! - `Nat.div a 0 = 0` (total division)
//! - `Nat.mod a 0 = a` (total modulo)
//!
//! Split from the translator module for the 500-line new-file limit.

use super::concrete_real::is_concrete_real_divisor;
use super::translator::LeanExprTranslator;
use super::{reject_unsound_domain_ty, AyError, AyResult};
use crate::bridge::expr_classifier::LogicalForm;
use crate::bridge::rat_smt::is_rat_or_real_type;
use ay::Term;
use ay_translate::{ops, TermTranslator, TranslationHost, TranslationTermHost};
use clean_kernel::{Expr, ExprKind, FVarId};

/// Check if a type expression represents `Nat`.
///
/// Used for dispatching Nat-specific total semantics (monus subtraction,
/// total division, total modulo) vs standard Int/Real operations.
pub(super) fn is_nat_type(ty: &Expr) -> bool {
    matches!(
        ty.strip_mdata().kind(),
        ExprKind::Const(name, _) if name.to_string() == "Nat"
    )
}

impl LeanExprTranslator {
    /// Translate arithmetic forms with type-specific Nat semantics.
    ///
    /// Nat operations have total/monus semantics:
    /// - `Nat.sub a b = max(a - b, 0)` (monus)
    /// - `Nat.div a 0 = 0` (total division)
    /// - `Nat.mod a 0 = a` (total modulo)
    pub(super) fn translate_arithmetic_form<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        form: LogicalForm,
    ) -> AyResult<Term> {
        match form {
            LogicalForm::Add { ty, lhs, rhs, .. } => {
                reject_unsound_domain_ty(&ty)?;
                let l = TermTranslator::translate(self, ctx, &lhs)?;
                let r = TermTranslator::translate(self, ctx, &rhs)?;
                Ok(ops::arith::add(ctx, l, r))
            }
            LogicalForm::Sub { ty, lhs, rhs, .. } => {
                reject_unsound_domain_ty(&ty)?;
                let l = TermTranslator::translate(self, ctx, &lhs)?;
                let r = TermTranslator::translate(self, ctx, &rhs)?;
                if is_nat_type(&ty) {
                    let cond = ops::compare(ctx, ops::Comparison::Ge, l, r);
                    let diff = ops::arith::sub(ctx, l, r);
                    let zero = ctx.solver().int_const(0);
                    Ok(ops::ite(ctx, cond, diff, zero))
                } else {
                    Ok(ops::arith::sub(ctx, l, r))
                }
            }
            LogicalForm::Mul { ty, lhs, rhs, .. } => {
                reject_unsound_domain_ty(&ty)?;
                let l = TermTranslator::translate(self, ctx, &lhs)?;
                let r = TermTranslator::translate(self, ctx, &rhs)?;
                Ok(ops::arith::mul(ctx, l, r))
            }
            LogicalForm::Div { ty, lhs, rhs, .. } => {
                reject_unsound_domain_ty(&ty)?;
                if is_nat_type(&ty) {
                    let l = TermTranslator::translate(self, ctx, &lhs)?;
                    let r = TermTranslator::translate(self, ctx, &rhs)?;
                    let zero = ctx.solver().int_const(0);
                    let rhs_positive = ops::compare(ctx, ops::Comparison::Gt, r, zero);
                    let div_result = ops::arith::int_div(ctx, l, r);
                    Ok(ops::ite(ctx, rhs_positive, div_result, zero))
                } else if is_rat_or_real_type(&ty) {
                    // Real/Rat: exact division with concrete denominator only (#2795, #3383)
                    // Rat maps to SMT Real (dense ordered field) and uses real division.
                    if !is_concrete_real_divisor(&rhs) {
                        return Err(AyError::UnsupportedExpr(
                            "Real/Rat division with symbolic denominator".to_string(),
                        ));
                    }
                    let l = TermTranslator::translate(self, ctx, &lhs)?;
                    let r = TermTranslator::translate(self, ctx, &rhs)?;
                    // Coerce Int-sorted operands to Real (e.g. bare Nat literals)
                    let l = coerce_int_to_real(ctx, l);
                    let r = coerce_int_to_real(ctx, r);
                    Ok(ops::arith::div(ctx, l, r))
                } else {
                    let l = TermTranslator::translate(self, ctx, &lhs)?;
                    let r = TermTranslator::translate(self, ctx, &rhs)?;
                    Ok(ops::arith::int_div(ctx, l, r))
                }
            }
            LogicalForm::Mod { ty, lhs, rhs, .. } => {
                reject_unsound_domain_ty(&ty)?;
                let l = TermTranslator::translate(self, ctx, &lhs)?;
                let r = TermTranslator::translate(self, ctx, &rhs)?;
                if is_nat_type(&ty) {
                    let zero = ctx.solver().int_const(0);
                    let rhs_positive = ops::compare(ctx, ops::Comparison::Gt, r, zero);
                    let mod_result = ops::arith::modulo(ctx, l, r);
                    Ok(ops::ite(ctx, rhs_positive, mod_result, l))
                } else {
                    Ok(ops::arith::modulo(ctx, l, r))
                }
            }
            LogicalForm::Neg { inner, .. } => {
                let a = TermTranslator::translate(self, ctx, &inner)?;
                Ok(ops::arith::neg(ctx, a))
            }
            _ => unreachable!("only arithmetic forms passed to translate_arithmetic_form"),
        }
    }
}

/// Coerce an Int-sorted ay term to Real sort via `to_real`.
///
/// No-op if the term is already Real-sorted. Used for Real division where
/// operands may be bare Nat/Int literals. Part of #2795.
fn coerce_int_to_real<V: Eq + core::hash::Hash, H: TranslationHost<V>>(
    ctx: &mut H,
    term: Term,
) -> Term {
    let sort = ctx.solver().term_sort(term);
    if sort.is_int() {
        ctx.solver()
            .try_int_to_real(term)
            .expect("invariant: sort.is_int() checked above")
    } else {
        term
    }
}
