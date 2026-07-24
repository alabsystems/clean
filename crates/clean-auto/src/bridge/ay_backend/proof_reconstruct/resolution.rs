// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolution proof reconstruction: ay Resolution steps → kernel proof terms.
//!
//! Binary resolution: clause1 contains `pivot`, clause2 contains `¬pivot`.
//! The resolvent is `(clause1 \ {pivot}) ∪ (clause2 \ {¬pivot})`.
//! Proof terms use nested `Or.rec` case analysis + `absurd` at the pivot.
//!
//! Planning (pivot orientation, position mapping) is in [`resolution_plan`].
//! Recursive proof synthesis is in [`resolution_build`].

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::resolution_build::ResolutionBuilder;
use super::resolution_plan::ResolutionPlan;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct a Resolution step.
    pub(super) fn reconstruct_resolution(
        &mut self,
        resolvent_clause: &[TermId],
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        // 1. Retrieve premise proof terms from step_cache
        let h1 = self.get_premise_proof(clause1, step_id)?;
        let h2 = self.get_premise_proof(clause2, step_id)?;

        // 2-7. Build resolution plan (bounds check, translate, pivot, positions, target)
        let plan = ResolutionPlan::build(self, resolvent_clause, pivot, clause1, clause2, step_id)?;

        // 8. Build the resolution proof term
        let builder = ResolutionBuilder::new(self, &plan);
        builder.build(&h1, &h2)
    }

    /// Look up a previously-reconstructed premise proof from the step cache.
    pub(super) fn get_premise_proof(
        &self,
        premise: ProofId,
        from_step: ProofId,
    ) -> ReconstructResult<Expr> {
        self.step_cache
            .get(premise.0 as usize)
            .and_then(|opt| opt.clone())
            .ok_or(ReconstructionError::InvalidPremise {
                premise: premise.0,
                from_step: from_step.0,
            })
    }

    /// Check if `a` is the negation of `b` (or vice versa) via the trace adapter.
    pub(super) fn is_negation_pair(&self, a: TermId, b: TermId) -> bool {
        self.trace().is_negation_pair(a, b)
    }

    /// Translate a clause's TermIds to kernel propositions.
    pub(super) fn translate_clause_props(
        &mut self,
        clause: &[TermId],
    ) -> ReconstructResult<Vec<Expr>> {
        clause.iter().map(|&t| self.translate_term(t)).collect()
    }
}
