// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    register_exists_witness_bindings, translate_expr_with_sync, AyResult, Expr, FVarId,
    SmtLibTranslator, SmtSolver,
};

impl SmtSolver {
    /// Translate and assert a Lean expression as a constraint
    ///
    /// This is a convenience method that translates the expression to an SMT term
    /// and immediately asserts it. Returns Ok(()) on success, or the translation error.
    ///
    /// # Contract
    ///
    /// REQUIRES: `expr` is a well-typed Lean proposition
    /// ENSURES: On Ok, `expr` is added as a constraint to the SMT solver
    /// ENSURES: On Err, the expression could not be translated, or solver is unavailable
    /// ENSURES: New declarations are synced to the proof backend (Verifiable path)
    #[cfg_attr(not(test), allow(dead_code))]
    pub(in super::super) fn translate_and_assert(&mut self, expr: &Expr) -> AyResult<()> {
        match self {
            SmtSolver::Fast(backend) => {
                let term = backend.translate_expr(expr)?;
                backend.assert_term(term);
                Ok(())
            }
            SmtSolver::Verifiable {
                backend,
                translator,
                var_map,
                ..
            } => {
                let translation = translate_expr_with_sync(backend, translator, var_map, expr)?;
                backend.assert_formula(&translation.formula);
                Ok(())
            }
            #[cfg(test)]
            SmtSolver::Disabled { reason, .. } => Err(
                clean_auto::bridge::ay_contract::AyError::SolverDisabled(reason.clone()),
            ),
        }
    }

    pub(in super::super) fn translate_and_assert_hypothesis(
        &mut self,
        hyp_fvar: FVarId,
        hyp_ty: &Expr,
    ) -> AyResult<()> {
        match self {
            SmtSolver::Fast(backend) => {
                let term = backend.translate_expr(hyp_ty)?;
                backend.assert_term(term);
                Ok(())
            }
            SmtSolver::Verifiable {
                backend,
                translator,
                var_map,
                exists_bindings,
                next_exists_placeholder_fvar,
                ..
            } => {
                let translation = translate_expr_with_sync(backend, translator, var_map, hyp_ty)?;
                backend.assert_formula(&translation.formula);
                var_map.register_hypothesis(
                    &SmtLibTranslator::canonical_fvar_name(hyp_fvar),
                    hyp_fvar,
                    Expr::fvar(hyp_fvar),
                    hyp_ty.clone(),
                );
                register_exists_witness_bindings(
                    var_map,
                    exists_bindings,
                    next_exists_placeholder_fvar,
                    hyp_fvar,
                    hyp_ty,
                    &translation.new_exists_skolemizations,
                )?;
                Ok(())
            }
            #[cfg(test)]
            SmtSolver::Disabled { reason, .. } => Err(
                clean_auto::bridge::ay_contract::AyError::SolverDisabled(reason.clone()),
            ),
        }
    }
}
