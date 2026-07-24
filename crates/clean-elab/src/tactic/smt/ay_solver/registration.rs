// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    is_exists_hypothesis, supported_local_decl_kind, sync_new_translator_declarations, AyError,
    AyResult, Expr, SmtSolver, SupportedLocalDeclKind,
};
use crate::tactic::LocalDecl;
use crate::unify::MetaState;

impl SmtSolver {
    /// Register all FVars from a goal's local context with sort inferred from
    /// their Lean types. Must be called before `translate_and_assert` or `prove`
    /// so that `translate_fvar` can look up the correct sort instead of
    /// defaulting to `Sort::Int` (#2129 AC1 fix).
    ///
    /// # Contract
    ///
    /// REQUIRES: `local_ctx` contains the goal's local declarations
    /// REQUIRES: `metas` contains current metavariable assignments
    /// ENSURES: Sort-valued locals are ignored because they never become SMT terms
    /// ENSURES: Supported term-valued FVars in `local_ctx` are registered with
    ///   their correct SMT sorts
    /// ENSURES: Only Prop-valued locals seed `VariableMapping`'s
    ///   hypothesis-proof entries; non-Prop scalar locals seed only term
    ///   back-translation state
    /// ENSURES: Unsupported non-sort local declaration types return
    ///   `AyError::UnsupportedExpr`
    /// ENSURES: Verifiable path keeps `VariableMapping` keyed by the
    ///   translator-owned SMT symbol for each local declaration
    pub(in super::super) fn register_fvars_from_context(
        &mut self,
        local_ctx: &[LocalDecl],
        metas: &MetaState,
    ) -> AyResult<()> {
        match self {
            SmtSolver::Fast(backend) => {
                for decl in local_ctx {
                    let ty = metas.instantiate(&decl.ty);
                    backend.register_fvar_from_lean_type(decl.fvar, &ty)?;
                }
                Ok(())
            }
            SmtSolver::Verifiable {
                backend,
                translator,
                var_map,
                next_exists_placeholder_fvar,
                ..
            } => {
                let next_placeholder_base = local_ctx
                    .iter()
                    .map(|decl| decl.fvar.as_u64().saturating_add(1))
                    .max()
                    .unwrap_or(0);
                if *next_exists_placeholder_fvar < next_placeholder_base {
                    *next_exists_placeholder_fvar = next_placeholder_base;
                }
                for decl in local_ctx {
                    let ty = metas.instantiate(&decl.ty);
                    let lean_ty = ty.strip_mdata();
                    if lean_ty.is_sort() && !lean_ty.is_prop() {
                        continue;
                    }
                    let Some(kind) = supported_local_decl_kind(&ty) else {
                        if is_exists_hypothesis(&ty) {
                            // `h : Exists ...` is a proof witness, not an SMT term.
                            // The hypothesis-aware assert path translates its type and
                            // records the reconstruction placeholders later.
                            continue;
                        }
                        return Err(AyError::UnsupportedExpr(format!(
                            "unsupported SMT local declaration type for {}: {:?}",
                            decl.name, ty
                        )));
                    };
                    match kind {
                        SupportedLocalDeclKind::Scalar(sort) => {
                            let decl_count_before = translator.declarations().len();
                            let smt_name =
                                translator.register_fvar(decl.fvar, sort, Expr::fvar(decl.fvar));
                            sync_new_translator_declarations(
                                backend,
                                translator,
                                decl_count_before,
                            );
                            // Register for term back-translation
                            var_map.register_var(&smt_name, Expr::fvar(decl.fvar), ty.clone());
                            if lean_ty.is_prop() {
                                // Only proof-typed locals replay through the
                                // hypothesis map; scalar terms reconstruct via
                                // `register_var`.
                                var_map.register_hypothesis(
                                    &smt_name,
                                    decl.fvar,
                                    Expr::fvar(decl.fvar),
                                    ty.clone(),
                                );
                            }
                        }
                        SupportedLocalDeclKind::Callable { result_sort } => {
                            translator.register_callable_fvar(
                                decl.fvar,
                                result_sort,
                                Expr::fvar(decl.fvar),
                                ty.clone(),
                            );
                        }
                    }
                }
                Ok(())
            }
            #[cfg(test)]
            SmtSolver::Disabled { .. } => Ok(()),
        }
    }
}
