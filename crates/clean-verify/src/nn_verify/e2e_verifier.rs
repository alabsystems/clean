// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end neural network verification pipeline orchestrator.
//!
//! Given a [`JsonCertificate`] from gamma-crown, this module:
//! 1. Converts the certificate to a Farkas chain
//! 2. Verifies each layer's Farkas certificate independently
//! 3. Checks interface consistency (layer i output = layer i+1 input)
//! 4. Composes certificates via T70 (entailment transitivity)
//! 5. Verifies the output property (robust classification margin)
//!
//! The IBP pipeline in [`super::pipeline`] computes bounds from scratch;
//! this module verifies pre-computed certificates (certificate-replay).

use super::certificate::farkas_bridge::{
    verify_farkas_certificate, ExternalFarkasCert, FarkasBridgeError, FarkasVerifyResult,
};
use super::certificate::farkas_chain::chain_farkas_certs;
use super::e2e_json_parser::{
    json_to_farkas_chain, JsonCertificate, JsonOutputProperty, PipelineParseError,
};
use super::ibp_crown::Interval;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Full verification result for a neural network certificate.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationResult {
    /// Whether the claimed property is verified.
    pub verified: bool,
    /// Per-layer verification results.
    pub layer_results: Vec<LayerVerifyResult>,
    /// Final composed Farkas certificate (if all layers pass).
    pub composed_cert: Option<ExternalFarkasCert>,
    /// Total verification steps performed (one per layer + composition + property check).
    pub verification_steps: usize,
    /// Trust level classification.
    pub trust_level: TrustLevel,
}

/// Trust level for the verification result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Fully verified: all Farkas certificates checked, composition valid.
    FullyVerified,
    /// Certificate-based: Farkas certificates verified but formal proofs are DerivedPending.
    CertificateBased,
    /// Partial: some layers verified, some failed.
    Partial {
        /// Number of verified layers.
        verified_layers: usize,
        /// Total number of layers.
        total_layers: usize,
    },
}

/// Verification result for a single layer.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct LayerVerifyResult {
    /// Layer index (0-based).
    pub layer_index: usize,
    /// Layer type string.
    pub layer_type: String,
    /// Whether the Farkas certificate is valid.
    pub farkas_valid: bool,
    /// Whether the bounds are structurally valid (non-empty, ordered).
    pub bounds_valid: bool,
    /// Input interval bounds (extracted from the Farkas certificate).
    pub input_interval: Option<Vec<Interval>>,
    /// Output interval bounds (extracted from the Farkas certificate).
    pub output_interval: Option<Vec<Interval>>,
}

/// Errors from the end-to-end verification pipeline.
#[derive(Debug)]
#[non_exhaustive]
pub enum E2eVerifyError {
    /// Certificate parsing or validation failed.
    ParseError(PipelineParseError),
    /// Farkas bridge error during chain composition.
    BridgeError(FarkasBridgeError),
}

impl std::fmt::Display for E2eVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ParseError(e) => write!(f, "parse error: {e}"),
            Self::BridgeError(e) => write!(f, "bridge error: {e}"),
        }
    }
}

impl std::error::Error for E2eVerifyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ParseError(e) => Some(e),
            Self::BridgeError(e) => Some(e),
        }
    }
}

impl From<PipelineParseError> for E2eVerifyError {
    fn from(e: PipelineParseError) -> Self {
        Self::ParseError(e)
    }
}

impl From<FarkasBridgeError> for E2eVerifyError {
    fn from(e: FarkasBridgeError) -> Self {
        Self::BridgeError(e)
    }
}

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

/// T73: End-to-end pipeline soundness.
///
/// If all layer Farkas certificates are valid and interface consistency holds,
/// then the composed certificate proves the end-to-end bound.
pub const T73_PIPELINE_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T74: Interface consistency implies composition validity.
///
/// If consecutive layers have matching output/input bounds, then the
/// Farkas chain composition succeeds and the result is valid.
pub const T74_INTERFACE_CONSISTENCY: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Pipeline entry point
// ---------------------------------------------------------------------------

/// Run the full end-to-end verification pipeline on a gamma-crown certificate.
///
/// Steps:
/// 1. Parse and validate the certificate structure
/// 2. Convert to Farkas chain
/// 3. Verify each layer's Farkas certificate
/// 4. Check interface consistency between adjacent layers
/// 5. Compose the chain (if all layers pass)
/// 6. Check the output property (classification robustness margin)
///
/// # Errors
///
/// Returns [`E2eVerifyError`] for parse or bridge failures. Note that
/// verification *failures* (invalid certificates, unverified properties) are
/// returned as `Ok(VerificationResult { verified: false, .. })`, not errors.
/// Errors indicate structural problems that prevent verification from running.
#[must_use = "verification result should be inspected"]
pub fn verify_network(cert: &JsonCertificate) -> Result<VerificationResult, E2eVerifyError> {
    // Step 1-2: Parse and convert to Farkas chain.
    let farkas_chain = json_to_farkas_chain(cert)?;
    let num_layers = farkas_chain.len();

    // Step 3: Verify each layer's Farkas certificate.
    let mut layer_results = Vec::with_capacity(num_layers);
    let mut all_valid = true;
    let mut verified_count = 0;

    for (i, farkas) in farkas_chain.iter().enumerate() {
        let result = verify_layer(farkas, i, &cert.layer_certs[i].layer_type);
        if result.farkas_valid && result.bounds_valid {
            verified_count += 1;
        } else {
            all_valid = false;
        }
        layer_results.push(result);
    }

    // Step 4: Check interface consistency.
    let interface_results = check_interface_consistency(&cert.layer_certs);
    let interfaces_consistent = interface_results.iter().all(|&(_, ok)| ok);
    if !interfaces_consistent {
        all_valid = false;
    }

    // Step 5: Compose the chain if all layers passed.
    let mut verification_steps = num_layers; // one per layer
    let composed_cert = if all_valid && farkas_chain.len() >= 2 {
        match compose_farkas_chain(&farkas_chain) {
            Ok(composed) => {
                verification_steps += farkas_chain.len() - 1; // composition steps
                Some(composed)
            }
            Err(_) => {
                all_valid = false;
                None
            }
        }
    } else if all_valid && farkas_chain.len() == 1 {
        Some(farkas_chain[0].clone())
    } else {
        None
    };

    // Step 6: Check output property.
    verification_steps += 1; // property check
    let property_verified = if all_valid {
        let last_layer = &cert.layer_certs[num_layers - 1];
        verify_output_property(&last_layer.output_bounds, &cert.output_property)
    } else {
        false
    };

    let verified = all_valid && property_verified;

    let trust_level = if verified {
        // All Farkas certs verified, but formal proofs are DerivedPending.
        TrustLevel::CertificateBased
    } else if verified_count > 0 {
        TrustLevel::Partial {
            verified_layers: verified_count,
            total_layers: num_layers,
        }
    } else {
        TrustLevel::Partial {
            verified_layers: 0,
            total_layers: num_layers,
        }
    };

    Ok(VerificationResult {
        verified,
        layer_results,
        composed_cert,
        verification_steps,
        trust_level,
    })
}

// ---------------------------------------------------------------------------
// Layer verification
// ---------------------------------------------------------------------------

/// Verify a single layer's Farkas certificate.
fn verify_layer(farkas: &ExternalFarkasCert, index: usize, layer_type: &str) -> LayerVerifyResult {
    let farkas_result = verify_farkas_certificate(farkas);
    let farkas_valid = farkas_result == FarkasVerifyResult::Valid;

    // Check that bounds are structurally valid (non-empty, finite).
    let bounds_valid = are_bounds_valid(farkas);

    // Extract interval bounds from the box constraints if valid.
    let (input_interval, output_interval) = if farkas_valid {
        let input_ivs = extract_intervals_from_box(
            &farkas.input_matrix,
            &farkas.input_bounds,
            farkas.input_dim,
        );
        let output_ivs = extract_intervals_from_box(
            &farkas.output_matrix,
            &farkas.output_bounds,
            farkas.output_dim,
        );
        (input_ivs, output_ivs)
    } else {
        (None, None)
    };

    LayerVerifyResult {
        layer_index: index,
        layer_type: layer_type.to_string(),
        farkas_valid,
        bounds_valid,
        input_interval,
        output_interval,
    }
}

/// Check whether the Farkas certificate has structurally valid bounds.
fn are_bounds_valid(farkas: &ExternalFarkasCert) -> bool {
    !farkas.input_matrix.is_empty()
        && !farkas.output_matrix.is_empty()
        && farkas.input_bounds.iter().all(|b| b.is_finite())
        && farkas.output_bounds.iter().all(|b| b.is_finite())
}

/// Try to extract interval bounds from box constraints.
///
/// Returns `None` if the constraints are not in box form.
fn extract_intervals_from_box(
    matrix: &[Vec<f64>],
    bounds: &[f64],
    dim: usize,
) -> Option<Vec<Interval>> {
    use super::certificate::farkas_bridge::box_constraints_to_interval;
    box_constraints_to_interval(matrix, bounds, dim).ok()
}

// ---------------------------------------------------------------------------
// Interface consistency
// ---------------------------------------------------------------------------

/// Check that consecutive layer bounds are consistent.
///
/// For each pair of adjacent layers, the output bounds of layer i must
/// match the input bounds of layer i+1 (within floating-point tolerance).
///
/// Returns a vector of `(interface_index, is_consistent)` pairs.
#[must_use]
pub fn check_interface_consistency(
    layers: &[super::e2e_json_parser::JsonLayerCert],
) -> Vec<(usize, bool)> {
    let mut results = Vec::with_capacity(layers.len().saturating_sub(1));
    for i in 0..layers.len().saturating_sub(1) {
        let prev_output = &layers[i].output_bounds;
        let next_input = &layers[i + 1].input_bounds;
        let consistent = bounds_match(prev_output, next_input);
        results.push((i, consistent));
    }
    results
}

/// Check whether two sets of bounds match within tolerance.
fn bounds_match(a: &[(f64, f64)], b: &[(f64, f64)]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter()
        .zip(b.iter())
        .all(|(&(al, au), &(bl, bu))| (al - bl).abs() < 1e-9 && (au - bu).abs() < 1e-9)
}

// ---------------------------------------------------------------------------
// Farkas chain composition
// ---------------------------------------------------------------------------

/// Compose a chain of Farkas certificates left-to-right.
fn compose_farkas_chain(
    chain: &[ExternalFarkasCert],
) -> Result<ExternalFarkasCert, FarkasBridgeError> {
    debug_assert!(!chain.is_empty(), "chain must not be empty");

    if chain.len() == 1 {
        return Ok(chain[0].clone());
    }

    let mut accumulated = chain[0].clone();
    for cert in &chain[1..] {
        accumulated = chain_farkas_certs(&accumulated, cert)?;
    }
    Ok(accumulated)
}

// ---------------------------------------------------------------------------
// Output property verification
// ---------------------------------------------------------------------------

/// Verify the output property given the final layer's output bounds.
///
/// For `"robust_classification"`: checks that for all possible outputs within
/// bounds, `output[true_class] - output[other] >= margin` for all other classes.
/// This is verified by checking `lower[true_class] - upper[other] >= margin`.
#[must_use]
pub fn verify_output_property(output_bounds: &[(f64, f64)], property: &JsonOutputProperty) -> bool {
    if property.property_type != "robust_classification" {
        // Unknown property type: cannot verify.
        return false;
    }

    if output_bounds.is_empty() {
        return false;
    }

    if property.true_class >= output_bounds.len() {
        return false;
    }

    let true_lower = output_bounds[property.true_class].0;

    for (i, &(_, other_upper)) in output_bounds.iter().enumerate() {
        if i == property.true_class {
            continue;
        }
        // For robust classification: min(true_class) - max(other) >= margin
        if true_lower - other_upper < property.margin - 1e-9 {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_constants() {
        assert!(matches!(T73_PIPELINE_SOUND, ProofStatus::DerivedPending));
        assert!(matches!(
            T74_INTERFACE_CONSISTENCY,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_verify_output_property_robust_classification() {
        // Class 0 lower=5.0, class 1 upper=3.0 => margin 2.0 >= 1.0 => verified
        let bounds = vec![(5.0, 7.0), (1.0, 3.0)];
        let prop = JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 1.0,
        };
        assert!(verify_output_property(&bounds, &prop));
    }

    #[test]
    fn test_verify_output_property_insufficient_margin() {
        // Class 0 lower=3.0, class 1 upper=3.0 => margin 0.0 < 1.0 => not verified
        let bounds = vec![(3.0, 5.0), (2.0, 3.0)];
        let prop = JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 1.0,
        };
        assert!(!verify_output_property(&bounds, &prop));
    }

    #[test]
    fn test_verify_output_property_unknown_type() {
        let bounds = vec![(1.0, 2.0)];
        let prop = JsonOutputProperty {
            property_type: "unknown_property".to_string(),
            true_class: 0,
            margin: 0.0,
        };
        assert!(!verify_output_property(&bounds, &prop));
    }

    #[test]
    fn test_verify_output_property_empty_bounds() {
        let prop = JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 0.0,
        };
        assert!(!verify_output_property(&[], &prop));
    }

    #[test]
    fn test_verify_output_property_true_class_out_of_range() {
        let bounds = vec![(1.0, 2.0)];
        let prop = JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 5,
            margin: 0.0,
        };
        assert!(!verify_output_property(&bounds, &prop));
    }

    #[test]
    fn test_bounds_match_equal() {
        let a = vec![(1.0, 2.0), (3.0, 4.0)];
        let b = vec![(1.0, 2.0), (3.0, 4.0)];
        assert!(bounds_match(&a, &b));
    }

    #[test]
    fn test_bounds_match_different_length() {
        let a = vec![(1.0, 2.0)];
        let b = vec![(1.0, 2.0), (3.0, 4.0)];
        assert!(!bounds_match(&a, &b));
    }

    #[test]
    fn test_bounds_match_slightly_different() {
        let a = vec![(1.0, 2.0)];
        let b = vec![(1.0, 2.5)];
        assert!(!bounds_match(&a, &b));
    }

    #[test]
    fn test_trust_level_partial_equality() {
        assert_eq!(
            TrustLevel::Partial {
                verified_layers: 1,
                total_layers: 3
            },
            TrustLevel::Partial {
                verified_layers: 1,
                total_layers: 3
            },
        );
        assert_ne!(TrustLevel::FullyVerified, TrustLevel::CertificateBased);
    }
}
