// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay::Term;
use ay_translate::TranslationTermHost;
use clean_kernel::expr::{BigNat, Literal};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::super::{bignat_to_bigint, AyError, AyResult};
use super::LeanExprTranslator;

impl LeanExprTranslator {
    /// Inner dispatch: translate by expression kind.
    pub(super) fn translate_inner<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        expr: &Expr,
    ) -> AyResult<Term> {
        match expr.kind() {
            ExprKind::FVar(fvar_id) => self.translate_fvar(ctx, *fvar_id),
            ExprKind::Lit(lit) => self.translate_literal(ctx, lit),
            ExprKind::Const(name, _) => Self::translate_const(ctx, name),
            ExprKind::App(_, _) => self.translate_app(ctx, expr),
            // MData is a transparent metadata wrapper; unwrap and translate inner.
            ExprKind::MData(_, inner) => self.translate_inner(ctx, inner),
            _ => Err(AyError::UnsupportedExpr(
                "unsupported expression kind for SMT translation".to_string(),
            )),
        }
    }

    /// Translate a free variable.
    ///
    /// Requires the FVar to be pre-registered via `register_fvar*()`.
    fn translate_fvar<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        fvar_id: FVarId,
    ) -> AyResult<Term> {
        let sort = {
            let st = self.state.borrow();
            match st.registered_fvars.get(&fvar_id) {
                Some(sort) => sort.clone(),
                None => {
                    return Err(AyError::UnsupportedExpr(format!(
                        "unregistered FVar {} — call register_fvar*() before translation",
                        fvar_id.as_u64()
                    )));
                }
            }
        };
        let name = format!("fvar_{}", fvar_id.as_u64());
        Ok(ctx.get_or_declare(fvar_id, &name, sort))
    }

    /// Translate a literal.
    fn translate_literal<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        lit: &Literal,
    ) -> AyResult<Term> {
        match lit {
            Literal::Nat(n) => Ok(Self::int_const_nat(ctx, n)),
            Literal::String(s) => {
                if let Some(&term) = self.state.borrow().string_constants.get(s.as_ref()) {
                    return Ok(term);
                }
                let term = ctx.fresh_const("str", ay::Sort::Int);
                self.state
                    .borrow_mut()
                    .string_constants
                    .insert(s.clone(), term);
                Ok(term)
            }
        }
    }

    /// Translate a constant reference.
    ///
    /// Handles Boolean constants and numeric zero/one constants for
    /// Nat, Int, Rat, and Real. The Rat constants map to Real sort
    /// (dense ordered field) matching the Rat→Real mapping in `head_family.rs`.
    fn translate_const<H: TranslationTermHost<FVarId>>(ctx: &mut H, name: &Name) -> AyResult<Term> {
        let name_str = name.to_string();
        match name_str.as_str() {
            "True" | "true" => Ok(ctx.solver().bool_const(true)),
            "False" | "false" => Ok(ctx.solver().bool_const(false)),
            // Nat zero/one → Int sort (matching Nat→Int mapping)
            "Nat.zero" => Ok(ctx.solver().int_const(0)),
            // Int zero → Int sort
            "Int.zero" => Ok(ctx.solver().int_const(0)),
            // Rat zero/one → Real sort (matching Rat→Real mapping in head_family.rs)
            "Rat.zero" => ctx
                .solver()
                .try_rational_const(0, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const 0 failed: {err}"))),
            "Rat.one" => ctx
                .solver()
                .try_rational_const(1, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const 1 failed: {err}"))),
            "Real.zero" => ctx
                .solver()
                .try_rational_const(0, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const 0 failed: {err}"))),
            "Real.one" => ctx
                .solver()
                .try_rational_const(1, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const 1 failed: {err}"))),
            _ => Err(AyError::UnsupportedExpr(format!(
                "unknown constant: {}",
                name_str
            ))),
        }
    }

    /// Create an integer constant from a Nat literal (arbitrary precision).
    fn int_const_nat<H: TranslationTermHost<FVarId>>(ctx: &mut H, value: &BigNat) -> Term {
        match value.to_u64().and_then(|n| i64::try_from(n).ok()) {
            Some(value) => ctx.solver().int_const(value),
            None => {
                let bigint = bignat_to_bigint(value);
                ctx.solver().int_const_bigint(&bigint)
            }
        }
    }
}
