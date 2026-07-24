// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{ExistsWitnessBinding, Expr, SmtSolver, SmtVerifyPolicy};

impl SmtSolver {
    /// Get the effective verify policy being used by this solver
    ///
    /// ENSURES: `Fast` maps to `TrustSolver`
    /// ENSURES: `Verifiable` and `Disabled` return their stored policy
    pub(in super::super) fn effective_policy(&self) -> SmtVerifyPolicy {
        match self {
            SmtSolver::Fast(_) => SmtVerifyPolicy::TrustSolver,
            SmtSolver::Verifiable { policy, .. } => *policy,
            SmtSolver::Disabled { policy, .. } => *policy,
        }
    }

    pub(crate) fn registered_var(&self, name: &str) -> Option<&(Expr, Expr)> {
        match self {
            SmtSolver::Verifiable { var_map, .. } => var_map.get_var(name),
            SmtSolver::Fast(_) | SmtSolver::Disabled { .. } => None,
        }
    }

    pub(crate) fn registered_hypothesis(
        &self,
        name: &str,
    ) -> Option<&(clean_kernel::FVarId, Expr, Expr)> {
        match self {
            SmtSolver::Verifiable { var_map, .. } => var_map.get_hypothesis(name),
            SmtSolver::Fast(_) | SmtSolver::Disabled { .. } => None,
        }
    }

    pub(crate) fn exists_witness_bindings(&self) -> &[ExistsWitnessBinding] {
        match self {
            SmtSolver::Verifiable {
                exists_bindings, ..
            } => exists_bindings,
            SmtSolver::Fast(_) | SmtSolver::Disabled { .. } => &[],
        }
    }
}
