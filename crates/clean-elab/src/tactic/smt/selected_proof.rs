// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared proof-selection and trust-accounting helpers for accepted proof terms.

use crate::tactic::ProofState;
use clean_kernel::Expr;

#[cfg(feature = "ay-smt")]
use super::bridge_reconstruction::BridgeProbeOutcome;
#[cfg(any(feature = "ay-smt", test))]
use super::bridge_reconstruction::BridgeReconstructionCandidate;
use super::trusted_subterms::count_embedded_trusted_ay_terms;
#[cfg(any(feature = "ay-smt", test))]
use clean_auto::bridge::ay_contract::ResidualTrustSource;

/// A direct proof term that has already been validated for use on the goal.
///
/// For direct ay proofs, `residual` carries the typed source classification
/// from the reconstruction gate so acceptance logging can distinguish residual
/// causes. Certificate-only and bridge callers pass `None`. Part of #2618.
#[derive(Debug, Clone)]
pub(super) struct SelectedDirectProof {
    proof: Expr,
    trust_subterm_count: usize,
    residual: Option<clean_auto::bridge::ay_contract::ResidualTrustSummary>,
}

impl SelectedDirectProof {
    pub(super) fn new(proof: Expr, trust_subterm_count: usize) -> Self {
        Self {
            proof,
            trust_subterm_count,
            residual: None,
        }
    }

    #[cfg(any(feature = "ay-smt", test))]
    #[cfg_attr(not(feature = "ay-smt"), allow(dead_code))]
    pub(super) fn with_residual(
        proof: Expr,
        trust_subterm_count: usize,
        residual: clean_auto::bridge::ay_contract::ResidualTrustSummary,
    ) -> Self {
        Self {
            proof,
            trust_subterm_count,
            residual: Some(residual),
        }
    }

    pub(super) fn into_parts_with_residual(
        self,
    ) -> (
        Expr,
        usize,
        Option<clean_auto::bridge::ay_contract::ResidualTrustSummary>,
    ) {
        (self.proof, self.trust_subterm_count, self.residual)
    }

    #[cfg(any(feature = "ay-smt", test))]
    fn selection_debt_class(&self) -> SelectionDebtClass {
        match self.residual.and_then(|summary| summary.primary()) {
            Some(ResidualTrustSource::LocalReconstructionGap) => SelectionDebtClass::DirectLocalGap,
            Some(ResidualTrustSource::ArithmeticBoundary) => {
                SelectionDebtClass::DirectArithmeticBoundary
            }
            Some(
                ResidualTrustSource::AletheTrustStep
                | ResidualTrustSource::TheoryLemmaBvBitBlast
                | ResidualTrustSource::TheoryLemmaArrayAxiom
                | ResidualTrustSource::TheoryLemmaGeneric,
            ) => SelectionDebtClass::DirectInherentResidual,
            Some(_) => SelectionDebtClass::DirectInherentResidual,
            None => SelectionDebtClass::CountOnlyDirect,
        }
    }
}

#[cfg(any(feature = "ay-smt", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VerifiedProofPreference {
    Direct,
    Bridge,
}

#[cfg(any(feature = "ay-smt", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SelectionDebtClass {
    CountOnlyDirect,
    DirectInherentResidual,
    DirectArithmeticBoundary,
    DirectLocalGap,
    BridgeValidated,
}

#[cfg(any(feature = "ay-smt", test))]
impl BridgeReconstructionCandidate {
    fn selection_debt_class(&self) -> SelectionDebtClass {
        SelectionDebtClass::BridgeValidated
    }
}

#[cfg(any(feature = "ay-smt", test))]
fn prefers_bridge_on_equal_trust_tie(
    direct: &SelectedDirectProof,
    bridge: &BridgeReconstructionCandidate,
) -> bool {
    bridge.trust_subterm_count == direct.trust_subterm_count
        && direct.selection_debt_class() == SelectionDebtClass::DirectLocalGap
        && bridge.selection_debt_class() == SelectionDebtClass::BridgeValidated
}

#[cfg(any(feature = "ay-smt", test))]
pub(super) fn choose_verified_proof_preference(
    direct: &SelectedDirectProof,
    bridge: Option<&BridgeReconstructionCandidate>,
) -> VerifiedProofPreference {
    let Some(bridge) = bridge else {
        return VerifiedProofPreference::Direct;
    };

    match bridge.trust_subterm_count.cmp(&direct.trust_subterm_count) {
        std::cmp::Ordering::Less => VerifiedProofPreference::Bridge,
        std::cmp::Ordering::Greater => VerifiedProofPreference::Direct,
        std::cmp::Ordering::Equal => {
            if prefers_bridge_on_equal_trust_tie(direct, bridge) {
                VerifiedProofPreference::Bridge
            } else {
                VerifiedProofPreference::Direct
            }
        }
    }
}

#[cfg(feature = "ay-smt")]
pub(super) enum SelectedProofChoice {
    Direct(SelectedDirectProof),
    Bridge(BridgeReconstructionCandidate),
}

#[cfg(feature = "ay-smt")]
pub(super) struct SelectableBridgeCandidate(Option<BridgeReconstructionCandidate>);

#[cfg(feature = "ay-smt")]
impl From<Option<BridgeReconstructionCandidate>> for SelectableBridgeCandidate {
    fn from(candidate: Option<BridgeReconstructionCandidate>) -> Self {
        Self(candidate)
    }
}

#[cfg(feature = "ay-smt")]
impl From<BridgeProbeOutcome> for SelectableBridgeCandidate {
    fn from(candidate: BridgeProbeOutcome) -> Self {
        Self(candidate.into_candidate())
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn choose_selected_proof(
    direct: SelectedDirectProof,
    bridge_candidate: impl Into<SelectableBridgeCandidate>,
    tactic_name: &str,
) -> SelectedProofChoice {
    let SelectableBridgeCandidate(bridge_candidate) = bridge_candidate.into();
    let direct_residual_primary = direct
        .residual
        .as_ref()
        .and_then(|summary| summary.primary());

    if choose_verified_proof_preference(&direct, bridge_candidate.as_ref())
        == VerifiedProofPreference::Bridge
    {
        if let Some(candidate) = bridge_candidate.as_ref() {
            if prefers_bridge_on_equal_trust_tie(&direct, candidate) {
                tracing::info!(
                    tactic = tactic_name,
                    direct_trust_subterm_count = direct.trust_subterm_count,
                    bridge_trust_subterm_count = candidate.trust_subterm_count,
                    direct_residual_primary = ?direct_residual_primary,
                    "equal-trust bridge candidate preferred over direct proof with local reconstruction gap"
                );
            }
        }
        SelectedProofChoice::Bridge(bridge_candidate.expect("bridge preference checked"))
    } else {
        SelectedProofChoice::Direct(direct)
    }
}

fn saturating_trust_count(trust_subterm_count: usize) -> u32 {
    match u32::try_from(trust_subterm_count) {
        Ok(count) => count,
        Err(_) => {
            tracing::warn!(
                trust_subterm_count,
                "embedded trustedAy count exceeded u32 range; saturating proof-state accounting"
            );
            u32::MAX
        }
    }
}

fn count_selected_proof_trust_with_expected(
    proof: &Expr,
    expected_trust_subterm_count: usize,
    tactic_name: &str,
    proof_kind: &str,
) -> usize {
    let recorded_trust = count_embedded_trusted_ay_terms(proof);
    debug_assert_eq!(
        recorded_trust, expected_trust_subterm_count,
        "{tactic_name}: {proof_kind} trust count drifted between selection and accounting"
    );
    recorded_trust
}

/// Mirror embedded trust debt for an accepted proof and assert the caller's
/// previously computed count still matches the selected proof term.
#[cfg(feature = "ay-smt")]
pub(super) fn record_selected_proof_trust_with_expected(
    state: &mut ProofState,
    proof: &Expr,
    expected_trust_subterm_count: usize,
    tactic_name: &str,
    proof_kind: &str,
) -> usize {
    let recorded_trust = count_selected_proof_trust_with_expected(
        proof,
        expected_trust_subterm_count,
        tactic_name,
        proof_kind,
    );
    if recorded_trust > 0 {
        state.record_trusted_ay_unclassified(saturating_trust_count(recorded_trust));
        tracing::info!(
            tactic = tactic_name,
            proof_kind,
            trust_subterm_count = recorded_trust,
            "selected proof carries embedded trustedAy sub-terms"
        );
    }
    recorded_trust
}

/// Record trust for an already-selected non-bridge proof without touching the
/// ay reconstruction-success counter. When the accepted proof carries a typed
/// `ResidualTrustSummary` from the direct ay lane, the structured source
/// breakdown is included in the trace log. Part of #2618.
pub(super) fn accept_selected_direct_proof(
    state: &mut ProofState,
    direct_proof: SelectedDirectProof,
    tactic_name: &str,
    proof_kind: &str,
) -> Expr {
    let (proof, expected_trust_subterm_count, residual) = direct_proof.into_parts_with_residual();
    let recorded_trust = count_selected_proof_trust_with_expected(
        &proof,
        expected_trust_subterm_count,
        tactic_name,
        proof_kind,
    );
    if recorded_trust > 0 {
        if let Some(ref summary) = residual {
            state.record_trusted_ay_residual(saturating_trust_count(recorded_trust), *summary);
            tracing::info!(
                tactic = tactic_name,
                proof_kind,
                trust_subterm_count = recorded_trust,
                residual_primary = ?summary.primary(),
                residual_alethe_trust = summary.alethe_trust_steps(),
                residual_arith_boundary = summary.arithmetic_boundary_steps(),
                residual_local_gap = summary.local_gap_steps(),
                "selected proof carries typed residual trustedAy sub-terms"
            );

            // Emit opt-in audit record for arithmetic-boundary hits (#2875).
            if summary.arithmetic_boundary_steps() > 0 {
                clean_auto::bridge::proof_trust::append_trust_boundary_audit_record(
                    &clean_auto::bridge::proof_trust::TrustBoundaryAuditRecord {
                        lane: "selected_direct_proof",
                        crate_name: "clean-elab",
                        test_name: std::thread::current()
                            .name()
                            .unwrap_or("unknown")
                            .to_string(),
                        tactic: Some(tactic_name.to_string()),
                        proof_kind: Some(proof_kind.to_string()),
                        subsystem: None,
                        description: None,
                        step_index: None,
                        arithmetic_boundary_steps: summary.arithmetic_boundary_steps(),
                        local_gap_steps: summary.local_gap_steps(),
                        trust_subterm_count: recorded_trust,
                    },
                );
            }
        } else {
            state.record_trusted_ay_unclassified(saturating_trust_count(recorded_trust));
            tracing::info!(
                tactic = tactic_name,
                proof_kind,
                trust_subterm_count = recorded_trust,
                "selected proof carries embedded trustedAy sub-terms"
            );
        }
    }
    proof
}
