// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Finalization helpers for accepted ay UNSAT reconstruction candidates.

#[cfg(feature = "ay-smt")]
use super::ay_solver::ExistsWitnessBinding;
#[cfg(feature = "ay-smt")]
use super::trusted_subterms::count_embedded_trusted_ay_terms;
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::TrustBudget;

/// Finalize an already accepted ay reconstruction candidate by recording the
/// success counter and wrapping the refutation into a proof of the original
/// goal. The candidate's trust count is already exact at the `clean-auto`
/// boundary; this layer only preserves it while changing proof shape from
/// `False` refutation to goal proof. The typed `ResidualTrustSummary` is
/// preserved alongside the count so downstream selection and logging can
/// distinguish residual sources without recomputation. Part of #302, #2618.
#[cfg(feature = "ay-smt")]
pub(super) fn finalize_kernel_reconstruction_candidate(
    prop: &clean_kernel::Expr,
    negated_prop: &clean_kernel::Expr,
    candidate: clean_auto::bridge::ay_contract::KernelReconstructionCandidate,
    exists_bindings: &[ExistsWitnessBinding],
) -> (
    clean_kernel::Expr,
    usize,
    clean_auto::bridge::ay_contract::ResidualTrustSummary,
) {
    let (refutation, negated_goal_fvar, quality, residual) = candidate.into_parts();
    let trust_subterm_count = quality.trust_count();

    super::record_ay_reconstruction_success();
    let refutation =
        super::ay_refutation::close_exists_witness_bindings(refutation, exists_bindings);
    let goal_proof = super::ay_refutation::wrap_refutation_as_goal_proof(
        prop,
        negated_prop,
        refutation,
        negated_goal_fvar,
    );
    debug_assert_eq!(
        count_embedded_trusted_ay_terms(&goal_proof),
        trust_subterm_count,
        "wrapping an accepted ay refutation changed its embedded trustedAy debt"
    );
    (goal_proof, trust_subterm_count, residual)
}

/// Run the full reconstruction pipeline: build the negated goal, request an
/// already accepted direct-ay candidate, and wrap its refutation. Part of #302.
#[cfg(feature = "ay-smt")]
pub(super) fn reconstruct_unsat_proof(
    backend: &clean_auto::bridge::ay_contract::AyProofBackend,
    var_map: &clean_auto::bridge::ay_contract::VariableMapping,
    exists_bindings: &[ExistsWitnessBinding],
    prop: &clean_kernel::Expr,
    budget: TrustBudget,
) -> Option<(
    clean_kernel::Expr,
    usize,
    clean_auto::bridge::ay_contract::ResidualTrustSummary,
)> {
    use clean_kernel::{name::Name, Expr};
    let negated_prop = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop.clone());
    let candidate =
        backend.attempt_kernel_reconstruction_with_budget(var_map, &negated_prop, budget)?;
    Some(finalize_kernel_reconstruction_candidate(
        prop,
        &negated_prop,
        candidate,
        exists_bindings,
    ))
}
