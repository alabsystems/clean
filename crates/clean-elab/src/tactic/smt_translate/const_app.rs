// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Atom boundary for constant-headed applications in the proof-producing
//! SMT-LIB2 translator.
//!
//! After #2810, semantic classification (boolean ops, equality, comparisons,
//! arithmetic, quantifiers) is handled by the shared `LogicalForm` classifier
//! via `classified.rs`. This module retains only the atom-specific leftovers
//! that are intentionally outside the shared classifier contract:
//!
//! - Concrete `Int.ofNat` / `Int.negSucc` and Real integer coercions
//! - Default fail-closed fallback for unrecognized constant applications

use super::{
    nat_literal_decimal, try_extract_concrete_int, try_extract_concrete_nat, SmtLibTranslator,
    SmtSort, TranslateError, TranslatedTerm,
};
use clean_kernel::expr::Literal;
use clean_kernel::{Expr, ExprKind, Name};

impl SmtLibTranslator {
    /// Translate an atom-boundary constant-headed application to SMT-LIB2.
    ///
    /// Called only for expressions that the shared classifier returned as
    /// `SmtLogicalForm::Atom`. Handles canonical concrete Int/Real constructors and
    /// fails closed on anything else.
    pub(super) fn translate_atom_const_app(
        &mut self,
        name: &Name,
        args: &[&Expr],
    ) -> Result<TranslatedTerm, TranslateError> {
        let rendered = name.to_string();
        match (rendered.as_str(), args.len()) {
            // Canonical Int constructors. Actual OfNat dictionaries are
            // reduced and kernel-checked by the environment-owning SMT caller.
            ("Int.ofNat" | "Int.negSucc", 1) if *name == Name::from_string(&rendered) => {
                let ExprKind::Lit(Literal::Nat(n)) = args[0].strip_mdata().kind() else {
                    return Err(TranslateError::UnsupportedExpr(format!(
                        "{name} with non-concrete argument"
                    )));
                };
                Ok(TranslatedTerm {
                    smt: if rendered == "Int.ofNat" {
                        nat_literal_decimal(n)
                    } else {
                        format!("(- (+ {} 1))", nat_literal_decimal(n))
                    },
                    sort: SmtSort::Int,
                })
            }
            // Constructor-form Real coercions — concrete integer values only (#2794)
            ("Real.ofNat", 1) => {
                let n = try_extract_concrete_nat(args[0]).ok_or_else(|| {
                    TranslateError::UnsupportedExpr(
                        "Real.ofNat with non-concrete argument".to_string(),
                    )
                })?;
                Ok(TranslatedTerm {
                    smt: format!("{n}.0"),
                    sort: SmtSort::Real,
                })
            }
            ("Real.ofInt", 1) => {
                let n = try_extract_concrete_int(args[0]).ok_or_else(|| {
                    TranslateError::UnsupportedExpr(
                        "Real.ofInt with non-concrete argument".to_string(),
                    )
                })?;
                if n >= 0 {
                    Ok(TranslatedTerm {
                        smt: format!("{n}.0"),
                        sort: SmtSort::Real,
                    })
                } else {
                    Ok(TranslatedTerm {
                        smt: format!("(- {}.0)", -n),
                        sort: SmtSort::Real,
                    })
                }
            }

            // Default: unsupported constant application
            _ => Err(TranslateError::UnsupportedExpr(format!(
                "unsupported constant application: {name}"
            ))),
        }
    }
}
