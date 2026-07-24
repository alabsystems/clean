// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Variable declaration elaboration: binder type validation.
//!
//! The `variable` command in Lean 4 introduces auto-bound implicit parameters
//! that are automatically prepended to subsequent definitions within the current
//! section/namespace scope. The actual accumulation and prepending is handled by
//! `FileContext` in the preprocessing layer. This module validates that each
//! binder's type is well-formed during elaboration so errors surface early.

use crate::ElabError;
use clean_kernel::Expr;
use clean_parser::SurfaceBinder;

use super::ElabCtx;

impl<'a> ElabCtx<'a> {
    /// Elaborate variable declaration binders for type validation.
    ///
    /// Each binder's type annotation is elaborated to verify it is well-formed.
    /// Binders without type annotations are elaborated as fresh sort metavariables
    /// (matching Lean 4 behavior for untyped variable binders). Earlier binders
    /// are pushed into scope so later binders can reference them (e.g.,
    /// `variable (α : Type) (x : α)`).
    ///
    /// # REQUIRES
    /// - `binders` are valid surface binders from the parser
    ///
    /// # ENSURES
    /// - All binder types are elaborated and checked for well-formedness
    /// - Local context is restored to its original state on return
    /// - Returns `Ok(())` if all binder types are valid
    pub(super) fn elab_variable_binders(
        &mut self,
        binders: &[SurfaceBinder],
    ) -> Result<(), ElabError> {
        let mut pushed_count: usize = 0;

        let result = self.elab_variable_binders_inner(binders, &mut pushed_count);

        // Restore local context: pop all pushed locals in reverse order
        for _ in 0..pushed_count {
            self.pop_local();
        }

        result
    }

    /// Inner loop: elaborate each binder and push it into scope.
    ///
    /// Tracks the number of successfully pushed locals in `pushed_count`
    /// so the caller can clean up on both success and error paths.
    fn elab_variable_binders_inner(
        &mut self,
        binders: &[SurfaceBinder],
        pushed_count: &mut usize,
    ) -> Result<(), ElabError> {
        for binder in binders {
            let binder_ty = if let Some(ty) = &binder.ty {
                let elaborated = self.elaborate(ty)?;
                let instantiated = self.metas.instantiate(&elaborated);
                self.metas.instantiate_levels(&instantiated)
            } else {
                // Untyped variable binder: create a fresh sort metavariable.
                // This matches the behavior in elab_def_body for omitted annotations.
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };

            // Verify the type is well-formed (inhabits some Sort)
            let _ = self.ensure_type_expr(&binder_ty)?;

            // Push into scope so subsequent binders can reference this one
            let _fvar = self.push_local(binder.name.clone(), binder_ty);
            *pushed_count += 1;
        }
        Ok(())
    }
}
