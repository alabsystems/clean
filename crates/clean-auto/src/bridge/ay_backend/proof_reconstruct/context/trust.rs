// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::TermId;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::{ReconstructResult, ReconstructionContext};

impl<'a> ReconstructionContext<'a> {
    /// Synthesize a `trustedAy` sub-term for a failed step's clause.
    ///
    /// When a step fails to reconstruct (e.g., TrustBoundary from LRA Farkas
    /// with symbolic endpoints, or UnsupportedStep for unhandled theory lemma
    /// kinds), this method builds a `@trustedAy.{0} clause_type` proof term
    /// for the step. This allows downstream resolution/ThResolution steps to
    /// reference the trusted proof instead of cascade-failing with
    /// `InvalidPremise`.
    ///
    /// Returns `None` if the clause literals cannot be translated to kernel
    /// expressions (e.g., ay terms not in the term store or var_map).
    ///
    /// Part of #302: converts full-proof cascade failures into partial-trust
    /// proofs that the tactic layer can compare against bridge reconstruction.
    pub(super) fn synthesize_trust_subterm_for_step(&mut self, step_idx: usize) -> Option<Expr> {
        let clause = self.trace().clause_of_step(step_idx);
        self.build_trusted_ay_subterm_for_clause(&clause)
            .inspect_err(|error| {
                tracing::debug!(
                    step = step_idx,
                    %error,
                    "trust subterm synthesis failed for step; step will have no proof term"
                );
            })
            .ok()
    }

    /// Build a `trustedAy` sub-term for a clause without mutating statistics.
    ///
    /// Explicit trust handlers and error fallback both reuse this helper, but
    /// the caller decides whether the step counts as an intentional trust
    /// sub-term or as an error-triggered fallback.
    pub(in super::super) fn build_trusted_ay_subterm_for_clause(
        &mut self,
        clause: &[TermId],
    ) -> ReconstructResult<Expr> {
        let clause_type = if clause.is_empty() {
            Expr::const_(Name::from_string("False"), vec![])
        } else {
            let clause_props = self.translate_clause_props(clause)?;
            crate::bridge::disjunction::or_chain_type(&clause_props)
        };
        let trusted_ay = Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]);
        Ok(Expr::app(trusted_ay, clause_type))
    }
}
