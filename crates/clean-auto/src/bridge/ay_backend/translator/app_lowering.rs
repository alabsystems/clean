// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay::{Sort, Term};
use ay_translate::{TermTranslator, TranslationTermHost};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId, Literal};

use super::super::concrete_real::{try_extract_concrete_int, try_extract_concrete_nat};
use super::super::{bignat_to_bigint, AyError, AyResult};
use super::LeanExprTranslator;
use crate::bridge::expr_classifier::{classify_expr, LogicalForm};

impl LeanExprTranslator {
    /// Translate a function application.
    pub(super) fn translate_app<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        expr: &Expr,
    ) -> AyResult<Term> {
        let head = expr.get_app_fn().strip_mdata();
        let args = expr.get_app_args();

        match head.kind() {
            ExprKind::Const(name, _) => {
                // Int.negSucc n is -(n + 1), so it must not pass through the
                // generic unary-negation classification. The proof-producing
                // contract has the same constructor boundary.
                if matches!(name.to_string().as_str(), "Int.ofNat" | "Int.negSucc") {
                    self.translate_atom_const_app(ctx, name, &args)
                } else {
                    match classify_expr(expr) {
                        LogicalForm::Atom(_) => self.translate_atom_const_app(ctx, name, &args),
                        form => self.translate_classified(ctx, form),
                    }
                }
            }
            ExprKind::FVar(fvar_id) => self.translate_fvar_app(ctx, *fvar_id, &args),
            _ => Err(AyError::UnsupportedExpr(
                "unsupported application head for SMT translation".to_string(),
            )),
        }
    }

    /// Translate an FVar-headed function application using uninterpreted
    /// functions.
    fn translate_fvar_app<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        fvar_id: FVarId,
        args: &[&Expr],
    ) -> AyResult<Term> {
        let return_sort = {
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

        let mut arg_terms = Vec::with_capacity(args.len());
        for arg in args {
            arg_terms.push(TermTranslator::translate(self, ctx, arg)?);
        }

        let cached_decl = {
            let st = self.state.borrow();
            st.fvar_func_decls.get(&fvar_id).cloned()
        };

        let func_decl = if let Some(decl) = cached_decl {
            if decl.arity() != arg_terms.len() {
                return Err(AyError::UnsupportedExpr(format!(
                    "FVar {} applied with {} args, but previously declared with arity {}",
                    fvar_id.as_u64(),
                    arg_terms.len(),
                    decl.arity()
                )));
            }
            let cached_domain = decl.domain();
            for (index, arg_term) in arg_terms.iter().enumerate() {
                let actual_sort = ctx.solver().term_sort(*arg_term);
                if cached_domain[index] != actual_sort {
                    return Err(AyError::TypeMismatch {
                        expected: format!(
                            "FVar {} arg {} domain sort {:?}",
                            fvar_id.as_u64(),
                            index,
                            cached_domain[index]
                        ),
                        got: format!("{actual_sort:?}"),
                    });
                }
            }
            decl
        } else {
            let arg_sorts: Vec<Sort> = arg_terms
                .iter()
                .map(|term| ctx.solver().term_sort(*term))
                .collect();
            let name = format!("uf_fvar_{}", fvar_id.as_u64());
            let decl = ctx
                .solver()
                .try_declare_fun(&name, &arg_sorts, return_sort)
                .map_err(|err| AyError::UnsupportedExpr(format!("declare_fun failed: {err}")))?;
            self.state
                .borrow_mut()
                .fvar_func_decls
                .insert(fvar_id, decl.clone());
            decl
        };

        ctx.solver()
            .try_apply(&func_decl, &arg_terms)
            .map_err(|err| AyError::UnsupportedExpr(format!("apply failed: {err}")))
    }

    /// Translate remaining Atom cases for const-headed applications.
    fn translate_atom_const_app<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        name: &Name,
        args: &[&Expr],
    ) -> AyResult<Term> {
        let name_str = name.to_string();
        let arity = args.len();

        if matches!(name_str.as_str(), "Int.ofNat" | "Int.negSucc") && arity == 1 {
            if *name != Name::from_string(&name_str) {
                return Err(AyError::UnsupportedExpr(format!(
                    "noncanonical integer constructor: {name_str}"
                )));
            }
            let ExprKind::Lit(Literal::Nat(n)) = args[0].strip_mdata().kind() else {
                return Err(AyError::UnsupportedExpr(format!(
                    "{name_str} with non-concrete argument"
                )));
            };
            let mut value = bignat_to_bigint(n);
            if name_str == "Int.negSucc" {
                value = -value - 1u8;
            }
            return Ok(ctx.solver().int_const_bigint(&value));
        }

        if name_str == "Exists" && arity == 2 {
            return self.translate_exists_const_fallback(ctx, args[0], args[1]);
        }

        if name_str == "Real.ofNat" && arity == 1 {
            let nat_value = try_extract_concrete_nat(args[0]).ok_or_else(|| {
                AyError::UnsupportedExpr("Real.ofNat with non-concrete argument".to_string())
            })?;
            let int_value = i64::try_from(nat_value).map_err(|_| {
                AyError::UnsupportedExpr("Real.ofNat value too large for i64".to_string())
            })?;
            return ctx
                .solver()
                .try_rational_const(int_value, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const failed: {err}")));
        }

        if name_str == "Real.ofInt" && arity == 1 {
            let int_value = try_extract_concrete_int(args[0]).ok_or_else(|| {
                AyError::UnsupportedExpr("Real.ofInt with non-concrete argument".to_string())
            })?;
            return ctx
                .solver()
                .try_rational_const(int_value, 1)
                .map_err(|err| AyError::UnsupportedExpr(format!("real const failed: {err}")));
        }

        Err(AyError::UnsupportedExpr(format!(
            "unknown constant application: {} with {} args",
            name_str, arity
        )))
    }
}
