// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate composition logic (T70, T71).
//!
//! Chains per-block entailment certificates into whole-network proofs.
//! Given two entailment certificates where the conclusion of the first
//! matches a premise of the second, produce a composed certificate that
//! proves the second's conclusion directly from the first's premises.
//!
//! ## Soundness
//!
//! Composition is sound because entailment is transitive over linear
//! constraints. If `P => Q` (cert A) and `Q, R => S` (cert B), then
//! `P, R => S` by substituting Q from A into B's premise slot.
//!
//! The composed certificate is verified independently after composition
//! to catch implementation bugs (defense-in-depth).

use clean_elab::cert::external::{
    verify_entailment_certificate, ExternalCertError, ExternalEntailmentCert,
    ExternalLinearConstraint,
};
use thiserror::Error;

/// Error during certificate composition.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CompositionError {
    /// The conclusion of cert A does not match any premise of cert B.
    #[error("no matching premise: conclusion of cert A does not match any premise of cert B")]
    NoMatchingPremise,

    /// Dimension mismatch between certificates.
    #[error("dimension mismatch: {0}")]
    DimensionMismatch(String),

    /// Individual certificate verification failed.
    #[error("certificate verification failed: {0}")]
    VerificationFailed(#[from] ExternalCertError),

    /// Composed certificate failed post-composition verification.
    #[error("composed certificate verification failed: {0}")]
    ComposedVerificationFailed(ExternalCertError),
}

/// Result of composing two entailment certificates.
#[derive(Debug, Clone)]
pub struct ComposedCert {
    /// The composed entailment certificate.
    pub certificate: ExternalEntailmentCert,
    /// Index of the premise in cert B that was replaced by cert A's premises.
    pub replaced_premise_index: usize,
    /// Number of premises from cert A that were spliced in.
    pub spliced_premise_count: usize,
}

/// Check if two linear constraints are structurally equal.
fn constraints_match(a: &ExternalLinearConstraint, b: &ExternalLinearConstraint) -> bool {
    if a.kind != b.kind {
        return false;
    }
    if a.constant != b.constant {
        return false;
    }
    if a.coefficients.len() != b.coefficients.len() {
        return false;
    }
    a.coefficients
        .iter()
        .all(|(var, coeff)| b.coefficients.get(var) == Some(coeff))
}

/// Compose two sequential entailment certificates.
///
/// Finds the premise in `cert_b` that matches `cert_a`'s conclusion, then
/// replaces it with `cert_a`'s premises. The resulting certificate proves
/// `cert_b`'s conclusion from `cert_a`'s premises plus `cert_b`'s remaining
/// premises.
///
/// Both input certificates are verified before composition, and the result
/// is verified after composition (defense-in-depth).
///
/// # Errors
///
/// - [`CompositionError::VerificationFailed`] if either input fails verification
/// - [`CompositionError::NoMatchingPremise`] if cert_a's conclusion does not
///   match any premise in cert_b
/// - [`CompositionError::ComposedVerificationFailed`] if the result fails
///   post-composition verification (indicates a composition bug)
pub fn compose_entailment_certs(
    cert_a: &ExternalEntailmentCert,
    cert_b: &ExternalEntailmentCert,
) -> Result<ComposedCert, CompositionError> {
    // Verify both inputs independently.
    verify_entailment_certificate(cert_a)?;
    verify_entailment_certificate(cert_b)?;

    // Find which premise of cert_b matches cert_a's conclusion.
    let match_index = cert_b
        .premises
        .iter()
        .position(|p| constraints_match(&cert_a.conclusion, p))
        .ok_or(CompositionError::NoMatchingPremise)?;

    let matched_multiplier = cert_b.multipliers[match_index];

    // Build the composed premises: cert_a's premises scaled by cert_b's
    // multiplier for the matched slot, plus cert_b's remaining premises.
    let mut composed_premises = Vec::new();
    let mut composed_multipliers = Vec::new();

    // Splice in cert_a's premises, each scaled by matched_multiplier * cert_a_mult.
    for (premise, mult_a) in cert_a.premises.iter().zip(cert_a.multipliers.iter()) {
        composed_premises.push(premise.clone());
        let scaled = mult_a.mul(matched_multiplier)?;
        composed_multipliers.push(scaled);
    }
    let spliced_count = cert_a.premises.len();

    // Add cert_b's non-matched premises.
    for (i, (premise, mult_b)) in cert_b
        .premises
        .iter()
        .zip(cert_b.multipliers.iter())
        .enumerate()
    {
        if i != match_index {
            composed_premises.push(premise.clone());
            composed_multipliers.push(*mult_b);
        }
    }

    let composed = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: composed_premises,
        multipliers: composed_multipliers,
        conclusion: cert_b.conclusion.clone(),
    };

    // Defense-in-depth: verify the composed certificate.
    verify_entailment_certificate(&composed)
        .map_err(CompositionError::ComposedVerificationFailed)?;

    Ok(ComposedCert {
        certificate: composed,
        replaced_premise_index: match_index,
        spliced_premise_count: spliced_count,
    })
}

/// Build a simple entailment certificate for testing.
///
/// Proves `coeff * var <= premise_bound` implies `coeff * var <= conclusion_bound`
/// when `premise_bound <= conclusion_bound`.
#[cfg(test)]
pub(crate) fn build_simple_entailment(
    var: &str,
    coeff: i64,
    premise_bound: i64,
    conclusion_bound: i64,
) -> ExternalEntailmentCert {
    use clean_elab::cert::external::{ConstraintKind, ExternalRational};
    use std::collections::BTreeMap;

    let mut coefficients = BTreeMap::new();
    coefficients.insert(var.to_string(), ExternalRational::from_int(coeff));

    ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coefficients.clone(),
            constant: ExternalRational::from_int(premise_bound),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients,
            constant: ExternalRational::from_int(conclusion_bound),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_elab::cert::external::{ConstraintKind, ExternalRational};
    use std::collections::BTreeMap;

    #[test]
    fn test_compose_simple_chain() {
        // cert_a: x <= 5 implies x <= 6
        let cert_a = build_simple_entailment("x", 1, 5, 6);
        // cert_b: x <= 6 implies x <= 8
        let cert_b = build_simple_entailment("x", 1, 6, 8);

        let composed =
            compose_entailment_certs(&cert_a, &cert_b).expect("simple chain should compose");

        assert_eq!(composed.replaced_premise_index, 0);
        assert_eq!(composed.spliced_premise_count, 1);
        // Composed proves: x <= 5 implies x <= 8
        assert_eq!(
            composed.certificate.conclusion.constant,
            ExternalRational::from_int(8)
        );
    }

    #[test]
    fn test_compose_no_match_returns_error() {
        // cert_a: x <= 5 implies x <= 6
        let cert_a = build_simple_entailment("x", 1, 5, 6);
        // cert_b: y <= 3 implies y <= 4 (different variable)
        let cert_b = build_simple_entailment("y", 1, 3, 4);

        let err = compose_entailment_certs(&cert_a, &cert_b)
            .expect_err("mismatched variables should fail");
        assert!(
            matches!(err, CompositionError::NoMatchingPremise),
            "expected NoMatchingPremise, got {err:?}"
        );
    }

    #[test]
    fn test_constraints_match_exact() {
        let mut coeffs = BTreeMap::new();
        coeffs.insert("x".to_string(), ExternalRational::from_int(1));

        let a = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant: ExternalRational::from_int(5),
        };
        let b = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs,
            constant: ExternalRational::from_int(5),
        };
        assert!(constraints_match(&a, &b));
    }

    #[test]
    fn test_constraints_match_different_kind() {
        let mut coeffs = BTreeMap::new();
        coeffs.insert("x".to_string(), ExternalRational::from_int(1));

        let a = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant: ExternalRational::from_int(5),
        };
        let b = ExternalLinearConstraint {
            kind: ConstraintKind::Lt,
            coefficients: coeffs,
            constant: ExternalRational::from_int(5),
        };
        assert!(!constraints_match(&a, &b));
    }

    #[test]
    fn test_constraints_match_different_constant() {
        let mut coeffs = BTreeMap::new();
        coeffs.insert("x".to_string(), ExternalRational::from_int(1));

        let a = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant: ExternalRational::from_int(5),
        };
        let b = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs,
            constant: ExternalRational::from_int(6),
        };
        assert!(!constraints_match(&a, &b));
    }
}
