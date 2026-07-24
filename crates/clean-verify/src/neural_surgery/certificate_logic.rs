// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate Verification Soundness
//!
//! Formalizes the meta-theorem: if `verify_certificate(cert, model)` returns
//! `true`, then the stated property holds for the model.
//!
//! A certificate bundles:
//! 1. The edit applied (rank-1 update parameters u, v)
//! 2. The pre-edit output bounds (from gamma-crown)
//! 3. The Lipschitz constant
//! 4. The computed post-edit bounds
//!
//! Verification checks that the post-edit bounds follow from the pre-edit
//! bounds via the Lipschitz bound propagation theorem.

use super::bound_propagation::{BoundPropagationSpec, LipschitzBound, OutputBound};
use super::edit_algebra::RankOneUpdate;
use super::NeuralSurgeryError;

/// Verdict from certificate verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificateVerdict {
    /// The certificate is sound: stated bounds follow from the evidence.
    Sound,
    /// The certificate is unsound: stated bounds do not follow.
    Unsound,
}

/// An edit certificate bundling an edit with its verified bounds.
#[derive(Debug, Clone)]
pub struct EditCertificate {
    /// The rank-1 update that was applied.
    pub edit: RankOneUpdate,
    /// Pre-edit output bounds verified by gamma-crown.
    pub pre_edit_bounds: OutputBound,
    /// Lipschitz constant of the network w.r.t. weights.
    pub lipschitz: LipschitzBound,
    /// Post-edit output bounds claimed by this certificate.
    pub claimed_post_edit_bounds: OutputBound,
}

/// Specification of certificate verification soundness.
#[derive(Debug)]
pub struct CertificateSpec {
    bound_spec: BoundPropagationSpec,
}

impl CertificateSpec {
    /// Create a new certificate specification.
    #[must_use]
    pub fn new() -> Self {
        Self {
            bound_spec: BoundPropagationSpec::new(),
        }
    }

    /// **Theorem (Certificate Soundness):**
    ///
    /// `verify_certificate(cert)` returns `Sound` if and only if the
    /// claimed post-edit bounds are at least as wide as the bounds
    /// derived from Lipschitz bound propagation.
    ///
    /// Formally: cert is sound iff
    ///   cert.claimed_post_edit_bounds.lower <= propagated.lower
    ///   AND cert.claimed_post_edit_bounds.upper >= propagated.upper
    ///
    /// where propagated = propagate_bound(pre_edit_bounds, lipschitz, ||edit||_F).
    #[must_use]
    pub fn verify_certificate(&self, cert: &EditCertificate) -> CertificateVerdict {
        let delta = cert.edit.frobenius_norm();
        let required =
            self.bound_spec
                .propagate_bound(&cert.pre_edit_bounds, &cert.lipschitz, delta);

        // The claimed bounds must be at least as conservative as the required bounds.
        // claimed.lower <= required.lower (claimed lower bound is at least as low)
        // claimed.upper >= required.upper (claimed upper bound is at least as high)
        let lower_ok = cert.claimed_post_edit_bounds.lower <= required.lower + f64::EPSILON;
        let upper_ok = cert.claimed_post_edit_bounds.upper >= required.upper - f64::EPSILON;

        if lower_ok && upper_ok {
            CertificateVerdict::Sound
        } else {
            CertificateVerdict::Unsound
        }
    }

    /// **Theorem (Sound Certificates Are Conservative):**
    ///
    /// If a certificate is sound, its claimed bounds contain the
    /// Lipschitz-derived bounds.
    pub fn verify_sound_is_conservative(
        &self,
        cert: &EditCertificate,
    ) -> Result<(), NeuralSurgeryError> {
        if self.verify_certificate(cert) != CertificateVerdict::Sound {
            return Err(NeuralSurgeryError::TheoremVerificationFailed {
                name: "sound_is_conservative".to_string(),
                reason: "certificate is not sound, theorem premise not met".to_string(),
            });
        }

        let delta = cert.edit.frobenius_norm();
        let required =
            self.bound_spec
                .propagate_bound(&cert.pre_edit_bounds, &cert.lipschitz, delta);

        if !cert.claimed_post_edit_bounds.contains(required.lower)
            || !cert.claimed_post_edit_bounds.contains(required.upper)
        {
            // This should never happen for a Sound certificate, but we verify
            // the meta-property: soundness implies containment.
            return Err(NeuralSurgeryError::TheoremVerificationFailed {
                name: "sound_is_conservative".to_string(),
                reason: "sound certificate does not contain derived bounds".to_string(),
            });
        }

        Ok(())
    }

    /// **Theorem (Zero Edit Certificate):**
    ///
    /// A certificate for a zero edit is sound iff the claimed bounds
    /// contain the pre-edit bounds.
    pub fn verify_zero_edit_certificate(
        &self,
        pre_edit_bounds: &OutputBound,
        claimed_bounds: &OutputBound,
    ) -> Result<CertificateVerdict, NeuralSurgeryError> {
        let cert = EditCertificate {
            edit: RankOneUpdate::zero(1, 1),
            pre_edit_bounds: *pre_edit_bounds,
            lipschitz: LipschitzBound::new(1.0),
            claimed_post_edit_bounds: *claimed_bounds,
        };

        let verdict = self.verify_certificate(&cert);

        // For zero edits, soundness should be equivalent to containment
        let contains = claimed_bounds.lower <= pre_edit_bounds.lower + f64::EPSILON
            && claimed_bounds.upper >= pre_edit_bounds.upper - f64::EPSILON;

        if (verdict == CertificateVerdict::Sound) != contains {
            return Err(NeuralSurgeryError::TheoremVerificationFailed {
                name: "zero_edit_certificate".to_string(),
                reason: format!(
                    "zero-edit soundness ({verdict:?}) inconsistent with containment ({contains})"
                ),
            });
        }

        Ok(verdict)
    }
}

impl Default for CertificateSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_sound_cert() -> EditCertificate {
        let edit = RankOneUpdate::new(vec![0.1, 0.2], vec![0.3]);
        let pre_bounds = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(2.0);
        let delta = edit.frobenius_norm();
        let slack = lip.constant() * delta;
        // Claimed bounds are exactly the Lipschitz-derived bounds
        EditCertificate {
            edit,
            pre_edit_bounds: pre_bounds,
            lipschitz: lip,
            claimed_post_edit_bounds: OutputBound::new(
                pre_bounds.lower - slack,
                pre_bounds.upper + slack,
            ),
        }
    }

    fn make_unsound_cert() -> EditCertificate {
        let edit = RankOneUpdate::new(vec![0.1, 0.2], vec![0.3]);
        let pre_bounds = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(2.0);
        // Claimed bounds are too tight (not accounting for Lipschitz slack)
        EditCertificate {
            edit,
            pre_edit_bounds: pre_bounds,
            lipschitz: lip,
            claimed_post_edit_bounds: pre_bounds, // same as pre-edit = too tight
        }
    }

    #[test]
    fn test_sound_certificate_accepted() {
        let spec = CertificateSpec::new();
        let cert = make_sound_cert();
        assert_eq!(spec.verify_certificate(&cert), CertificateVerdict::Sound);
    }

    #[test]
    fn test_unsound_certificate_rejected() {
        let spec = CertificateSpec::new();
        let cert = make_unsound_cert();
        assert_eq!(spec.verify_certificate(&cert), CertificateVerdict::Unsound);
    }

    #[test]
    fn test_sound_is_conservative() {
        let spec = CertificateSpec::new();
        let cert = make_sound_cert();
        spec.verify_sound_is_conservative(&cert)
            .expect("sound certificate should be conservative");
    }

    #[test]
    fn test_conservative_fails_on_unsound() {
        let spec = CertificateSpec::new();
        let cert = make_unsound_cert();
        assert!(
            spec.verify_sound_is_conservative(&cert).is_err(),
            "should fail on unsound certificate"
        );
    }

    #[test]
    fn test_zero_edit_sound() {
        let spec = CertificateSpec::new();
        let pre = OutputBound::new(-1.0, 1.0);
        let claimed = OutputBound::new(-1.0, 1.0);
        let verdict = spec
            .verify_zero_edit_certificate(&pre, &claimed)
            .expect("zero edit check should succeed");
        assert_eq!(verdict, CertificateVerdict::Sound);
    }

    #[test]
    fn test_zero_edit_unsound() {
        let spec = CertificateSpec::new();
        let pre = OutputBound::new(-1.0, 1.0);
        let claimed = OutputBound::new(-0.5, 0.5); // too tight
        let verdict = spec
            .verify_zero_edit_certificate(&pre, &claimed)
            .expect("zero edit check should succeed");
        assert_eq!(verdict, CertificateVerdict::Unsound);
    }

    #[test]
    fn test_overcautious_certificate_is_sound() {
        let spec = CertificateSpec::new();
        let edit = RankOneUpdate::new(vec![0.1], vec![0.1]);
        let pre_bounds = OutputBound::new(0.0, 1.0);
        let lip = LipschitzBound::new(1.0);
        // Very conservative claimed bounds
        let cert = EditCertificate {
            edit,
            pre_edit_bounds: pre_bounds,
            lipschitz: lip,
            claimed_post_edit_bounds: OutputBound::new(-100.0, 100.0),
        };
        assert_eq!(
            spec.verify_certificate(&cert),
            CertificateVerdict::Sound,
            "overly conservative bounds should still be sound"
        );
    }
}
