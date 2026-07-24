// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof verification and kernel-reconstruction policy for AyProofBackend.

use super::AyProofBackend;
use crate::bridge::ay_backend::carcara_verify::verify_alethe_proof;
use crate::bridge::ay_backend::reconstruction_quality::{
    accept_kernel_reconstruction_candidate, KernelReconstructionCandidate, TrustBudget,
};
use crate::bridge::ay_backend::{AyError, AyResult};
use ay::ProofQuality;

impl AyProofBackend {
    /// Verify the proof if the proof profile requires verification
    ///
    /// Uses native ay-proof checker (preferred) or Carcara (fallback) for tier 1.
    /// See `designs/2026-03-01-smt-proof-verification-pipeline.md` for design.
    pub(super) fn verify_proof_if_required(
        &self,
        proof: &Option<String>,
        quality: &Option<ProofQuality>,
    ) -> AyResult<bool> {
        let profile = match self.config.profile() {
            Some(p) if p.verification_tier() >= 1 => p,
            _ => return Ok(false), // Tier 0 or no profile = not verified
        };

        // Check theory acceptance via the shared gate
        self.ensure_profile_accepts_current_logic()?;

        // Tier 1: Native ay-proof verification (preferred) or Carcara (fallback)
        if profile.verification_tier() == 1 {
            // Accept only if native check passed AND proof is complete (no trust/hole steps).
            // Incomplete proofs fall through to Carcara fallback (#2258).
            if quality.as_ref().is_some_and(|q| q.is_complete()) {
                return Ok(true);
            }

            // Fallback: Carcara verification (if feature enabled and proof available)
            let proof_str = proof.as_ref().ok_or_else(|| {
                AyError::VerificationFailed(
                    "proof required for tier 1 verification but not available".to_string(),
                )
            })?;

            match verify_alethe_proof(&self.last_problem, proof_str) {
                Ok(true) => return Ok(true),
                Ok(false) => {
                    return Err(AyError::VerificationFailed(
                        "Carcara rejected proof as invalid".to_string(),
                    ));
                }
                Err(error) => return Err(error.into()),
            }
        }

        // Tier 2+: Not yet implemented
        if profile.verification_tier() >= 2 {
            return Err(AyError::VerificationFailed(format!(
                "verification tier {} not yet implemented",
                profile.verification_tier()
            )));
        }

        Ok(false)
    }

    /// Attempt Tier 3 kernel proof reconstruction from the last UNSAT proof.
    ///
    /// Returns a closed refutation candidate only when reconstruction produced
    /// a proof term that derives the empty clause and does not contain open
    /// compound-witness FVars. Embedded `trustedAy` sub-terms are preserved and
    /// counted exactly on the accepted refutation.
    pub fn attempt_kernel_reconstruction(
        &self,
        var_map: &crate::bridge::ay_backend::proof_reconstruct::VariableMapping,
        negated_goal: &clean_kernel::Expr,
    ) -> Option<KernelReconstructionCandidate> {
        self.attempt_kernel_reconstruction_with_budget(
            var_map,
            negated_goal,
            TrustBudget::Unlimited,
        )
    }

    /// Attempt Tier 3 kernel proof reconstruction from the last UNSAT proof
    /// using the requested trust budget.
    ///
    /// `TrustBudget::ZeroTrust` rejects any reconstruction candidate that still
    /// embeds `trustedAy`, while `TrustBudget::Unlimited` preserves the legacy
    /// behavior. This is the policy-controlled direct-proof acceptance boundary
    /// used by the strict SMT verification lane.
    pub fn attempt_kernel_reconstruction_with_budget(
        &self,
        var_map: &crate::bridge::ay_backend::proof_reconstruct::VariableMapping,
        negated_goal: &clean_kernel::Expr,
        budget: TrustBudget,
    ) -> Option<KernelReconstructionCandidate> {
        match self.executor.last_proof() {
            Some(raw_proof) => accept_kernel_reconstruction_candidate(
                crate::bridge::ay_backend::proof_reconstruct::attempt_reconstruction(
                    raw_proof,
                    self.executor.terms(),
                    var_map,
                    negated_goal,
                ),
                budget,
            ),
            None => None,
        }
    }
}
