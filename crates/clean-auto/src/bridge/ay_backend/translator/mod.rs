// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean-local translator adapter implementing ay-translate consumer traits.
//!
//! `LeanExprTranslator` owns clean-specific translation caches behind interior
//! mutability (`RefCell`) and implements `SortTranslator` + `TermTranslator`.
//! `AyBackend` delegates to this translator so the lowering logic works against
//! any `TranslationTermHost<FVarId>`: both `TranslationContext` and
//! `TranslationSession`.
//!
//! Design: `designs/2026-03-11-2282-ay-translate-consumer-trait-adapter.md`

mod app_lowering;
mod classified;
mod state;
mod term_lowering;

use std::cell::RefCell;

use ay::{Sort, Term};
use ay_translate::{SortTranslator, TermTranslator, TranslationTermHost};
use clean_kernel::{Expr, FVarId};

use self::state::LeanTranslationState;
use super::{infer_sort_from_lean_type, AyError};

/// clean-local translator implementing `ay_translate::SortTranslator` and
/// `ay_translate::TermTranslator`.
///
/// Owns all clean-specific translation caches. The `AyBackend` keeps solver
/// and context ownership and delegates expression lowering to this translator.
#[derive(Default)]
pub(crate) struct LeanExprTranslator {
    state: RefCell<LeanTranslationState>,
}

impl SortTranslator for LeanExprTranslator {
    type Sort = Expr;
    type Error = AyError;

    fn translate_sort(&self, sort: &Expr) -> Result<Sort, AyError> {
        infer_sort_from_lean_type(sort)
    }
}

impl TermTranslator for LeanExprTranslator {
    type Expr = Expr;
    type VarKey = FVarId;
    type Error = AyError;

    fn translate<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        expr: &Expr,
    ) -> Result<Term, AyError> {
        crate::bridge::stack_safe(|| {
            if let Some(&term) = self.state.borrow().expr_to_term.get(expr) {
                return Ok(term);
            }

            let term = self.translate_inner(ctx, expr)?;
            self.state
                .borrow_mut()
                .expr_to_term
                .insert(expr.clone(), term);
            Ok(term)
        })
    }
}

impl LeanExprTranslator {
    /// Register a typed free variable (must be called before `translate`).
    pub(crate) fn register_fvar<H: TranslationTermHost<FVarId>>(
        &self,
        ctx: &mut H,
        fvar_id: FVarId,
        sort: Sort,
    ) -> Term {
        self.state
            .borrow_mut()
            .registered_fvars
            .insert(fvar_id, sort.clone());
        let name = format!("fvar_{}", fvar_id.as_u64());
        ctx.get_or_declare(fvar_id, &name, sort)
    }
}
