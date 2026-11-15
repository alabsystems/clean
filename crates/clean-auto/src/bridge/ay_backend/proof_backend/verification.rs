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
use ay::{CarcaraSurface, ProofQuality};

/// The stable marker every D7 external-recheck-surface refusal carries.
///
/// The Carcara round-trip's own failures (`no checker available`,
/// `Carcara rejected proof`, `Carcara verification error`) never carry it, so
/// a reader can tell "refused before Carcara, on ay's disclosure" from
/// "Carcara ran and said no".
pub(super) const CARCARA_SURFACE_REFUSAL_MARKER: &str = "ay D7 disclosure";

/// Why the tier-1 Carcara fallback refuses a script that used `push`/`pop`.
pub(super) const SCOPED_SCRIPT_REFUSAL: &str =
    "the script uses push/pop, and Carcara checks a problem as one query without scopes \
     (third-party/carcara/DOWNSTREAM.md, fix 37); refused before invoking Carcara";

impl AyProofBackend {
    /// Refuse the tier-1 Carcara fallback unless ay disclosed that pinned
    /// Carcara can parse the certificate it rendered.
    ///
    /// Owner decision D7 (2026-09-22): ay renders every UNSAT proof its strict
    /// checker accepted and DISCLOSES the external-recheck surface
    /// (`Executor::last_unsat_proof_carcara_surface`) instead of withholding
    /// the document. A consumer that CLAIMS an external Carcara check — the
    /// tier-1 fallback does — must refuse an unsupported surface with ay's
    /// reason BEFORE invoking Carcara, never hand Carcara a document it cannot
    /// parse and report the parse failure as a verdict.
    ///
    /// Fail-closed on everything but `Supported`: `CarcaraSurface` is
    /// `#[non_exhaustive]`, so a variant this build does not know is refused,
    /// never read as checked; and an absent disclosure (no retained UNSAT
    /// proof) is refused, because nothing then vouches for the document's
    /// surface.
    fn refuse_unless_carcara_surface_supported(&self) -> AyResult<()> {
        // TODO(ay pin move, D7 precision): this disclosure is scanned with
        // ay's `last_proof_term_overrides`, but the document handed to Carcara
        // (`try_export_last_proof_alethe_for_problem_scope`) is rendered with
        // `proof_export_term_overrides` or the finite-enum table, so the two
        // can disagree. Either way it fails closed: under-reporting brings back
        // Carcara's parse error, and over-reporting refuses a document Carcara
        // might accept. ay's `carcara_surface_for_last_export(false)` reads the
        // document's own table but is `pub(crate)` at f28345ff. Make it public
        // in ay, or return the surface with the export, then switch this read
        // to it.
        let refusal = match self.executor.last_unsat_proof_carcara_surface() {
            Some(CarcaraSurface::Supported) => return Ok(()),
            Some(CarcaraSurface::Unsupported { reason }) => format!(
                "{CARCARA_SURFACE_REFUSAL_MARKER}: carcara_surface=unsupported: {reason}; \
                 pinned Carcara cannot parse this certificate, so tier 1 refuses the \
                 external-check claim before invoking Carcara"
            ),
            Some(unknown) => format!(
                "{CARCARA_SURFACE_REFUSAL_MARKER}: carcara_surface={unknown} is a surface \
                 verdict this consumer does not know; refused as unsupported, never read \
                 as checked"
            ),
            None => format!(
                "{CARCARA_SURFACE_REFUSAL_MARKER}: no retained UNSAT proof discloses a \
                 carcara_surface for this certificate; refused before invoking Carcara"
            ),
        };
        Err(AyError::VerificationFailed(refusal))
    }

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

            // Carcara reads `last_problem` as one query and refuses `push`/`pop`
            // (third-party/carcara/DOWNSTREAM.md, fix 37); before that fix it read every
            // popped assertion as a premise. Say so here, before invoking it.
            if self.uses_scopes() {
                return Err(AyError::VerificationFailed(
                    SCOPED_SCRIPT_REFUSAL.to_string(),
                ));
            }

            // D7: the external-check claim is made here, so the disclosure is
            // read here — before Carcara ever sees the document.
            self.refuse_unless_carcara_surface_supported()?;

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
    pub(crate) fn attempt_kernel_reconstruction(
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
