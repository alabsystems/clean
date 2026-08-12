// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON certificate parsing for gamma-crown verification certificates.
//!
//! Parses neural network verification certificates from a minimal JSON-like
//! format (struct-literal construction in practice, since we do not depend on
//! serde_json in this crate) and converts them to the internal
//! [`ExternalFarkasCert`] chain for the Farkas verification pipeline.
//!
//! ## Design
//!
//! The primary value is in [`json_to_farkas_chain`], which converts a
//! parsed [`JsonCertificate`] into a sequence of [`ExternalFarkasCert`]s
//! suitable for chaining via [`super::certificate::farkas_chain::chain_farkas_certs`].
//! Each layer certificate becomes one Farkas certificate encoding:
//!   input ∈ box(input_bounds) => output ∈ box(output_bounds)

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use super::certificate::farkas_bridge::{interval_to_box_constraints, ExternalFarkasCert};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A verification certificate from gamma-crown.
///
/// Encodes the full result of a neural network robustness verification run:
/// the network identity, per-layer certificates with multipliers and bounds,
/// the input perturbation specification, and the claimed output property.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct JsonCertificate {
    /// Network identifier (e.g., model name or hash).
    pub network_id: String,
    /// Number of layers verified.
    pub num_layers: usize,
    /// Per-layer certificates, ordered from input to output.
    pub layer_certs: Vec<JsonLayerCert>,
    /// Input specification (perturbation bounds).
    pub input_spec: JsonInputSpec,
    /// Claimed output property.
    pub output_property: JsonOutputProperty,
}

/// Certificate data for a single layer.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct JsonLayerCert {
    /// Layer index (0-based).
    pub layer_index: usize,
    /// Layer type: `"linear"`, `"relu"`, `"conv"`, `"layernorm"`.
    pub layer_type: String,
    /// Farkas multipliers for this layer's certificate.
    pub multipliers: Vec<f64>,
    /// Per-dimension input bounds as (lower, upper) pairs.
    pub input_bounds: Vec<(f64, f64)>,
    /// Per-dimension output bounds as (lower, upper) pairs.
    pub output_bounds: Vec<(f64, f64)>,
    /// Weight matrix for linear layers (row-major, output_dim x input_dim).
    pub weight_matrix: Option<Vec<Vec<f64>>>,
    /// Bias vector for linear layers.
    pub bias: Option<Vec<f64>>,
    /// Per-neuron activation status for ReLU layers from gamma-crown.
    ///
    /// Values: `"stable_active"`, `"stable_inactive"`, or `"unstable"`.
    /// Empty/None for non-ReLU layers. Used by gamma-crown to track which
    /// neurons have fixed activation status across the input region.
    pub activation_pattern: Option<Vec<String>>,
}

/// Input perturbation specification.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct JsonInputSpec {
    /// Center point of the input region.
    pub center: Vec<f64>,
    /// L-infinity perturbation radius.
    pub epsilon: f64,
}

/// Claimed output property to verify.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct JsonOutputProperty {
    /// Property type (e.g., `"robust_classification"`).
    pub property_type: String,
    /// True class index for classification robustness.
    pub true_class: usize,
    /// Required margin: output[true_class] - output[other] >= margin.
    pub margin: f64,
}

/// Errors from certificate parsing and conversion.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum PipelineParseError {
    /// The input is not valid (structural or format error).
    InvalidJson(String),
    /// A required field is missing from the certificate.
    MissingField(String),
    /// Dimension mismatch within a layer certificate.
    DimensionMismatch {
        /// Layer index where the mismatch occurred.
        layer: usize,
        /// Expected dimension.
        expected: usize,
        /// Actual dimension.
        got: usize,
    },
    /// Unsupported or invalid layer type.
    InvalidLayerType(String),
    /// Layer count in header does not match actual layer certificates.
    LayerCountMismatch {
        /// Declared layer count.
        declared: usize,
        /// Actual number of layer certificates.
        actual: usize,
    },
    /// Negative multiplier found in a layer certificate.
    NegativeMultiplier {
        /// Layer index.
        layer: usize,
        /// Multiplier index.
        index: usize,
        /// The negative value.
        value: f64,
    },
    /// Empty bounds (zero-dimensional layer).
    EmptyBounds {
        /// Layer index.
        layer: usize,
    },
}

impl std::fmt::Display for PipelineParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidJson(msg) => write!(f, "invalid JSON: {msg}"),
            Self::MissingField(field) => write!(f, "missing field: {field}"),
            Self::DimensionMismatch {
                layer,
                expected,
                got,
            } => {
                write!(
                    f,
                    "layer {layer}: dimension mismatch (expected {expected}, got {got})"
                )
            }
            Self::InvalidLayerType(t) => write!(f, "invalid layer type: {t}"),
            Self::LayerCountMismatch { declared, actual } => {
                write!(f, "layer count mismatch: declared {declared}, got {actual}")
            }
            Self::NegativeMultiplier {
                layer,
                index,
                value,
            } => {
                write!(
                    f,
                    "layer {layer}: negative multiplier at index {index}: {value}"
                )
            }
            Self::EmptyBounds { layer } => write!(f, "layer {layer}: empty bounds"),
        }
    }
}

impl std::error::Error for PipelineParseError {}

// ---------------------------------------------------------------------------
// Supported layer types
// ---------------------------------------------------------------------------

/// Recognized layer type strings.
const LAYER_TYPE_LINEAR: &str = "linear";
const LAYER_TYPE_RELU: &str = "relu";
const LAYER_TYPE_CONV: &str = "conv";
const LAYER_TYPE_LAYERNORM: &str = "layernorm";

/// Check whether a layer type string is recognized.
#[must_use]
fn is_valid_layer_type(layer_type: &str) -> bool {
    matches!(
        layer_type,
        LAYER_TYPE_LINEAR | LAYER_TYPE_RELU | LAYER_TYPE_CONV | LAYER_TYPE_LAYERNORM
    )
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/// Validate a [`JsonCertificate`] for structural consistency.
///
/// Checks layer count consistency, layer type validity, dimension matching
/// between adjacent layers, multiplier non-negativity, and bound ordering.
///
/// # Errors
///
/// Returns the first validation error found.
pub fn validate_certificate(cert: &JsonCertificate) -> Result<(), PipelineParseError> {
    // Layer count consistency.
    if cert.num_layers != cert.layer_certs.len() {
        return Err(PipelineParseError::LayerCountMismatch {
            declared: cert.num_layers,
            actual: cert.layer_certs.len(),
        });
    }

    if cert.layer_certs.is_empty() {
        return Err(PipelineParseError::MissingField("layer_certs".to_string()));
    }

    // Input spec consistency with first layer.
    let first_input_dim = cert.layer_certs[0].input_bounds.len();
    if cert.input_spec.center.len() != first_input_dim {
        return Err(PipelineParseError::DimensionMismatch {
            layer: 0,
            expected: first_input_dim,
            got: cert.input_spec.center.len(),
        });
    }

    for (i, layer) in cert.layer_certs.iter().enumerate() {
        validate_layer(layer, i)?;

        // Check inter-layer dimension consistency.
        if i > 0 {
            let prev_output_dim = cert.layer_certs[i - 1].output_bounds.len();
            let this_input_dim = layer.input_bounds.len();
            if prev_output_dim != this_input_dim {
                return Err(PipelineParseError::DimensionMismatch {
                    layer: i,
                    expected: prev_output_dim,
                    got: this_input_dim,
                });
            }
        }
    }

    Ok(())
}

/// Validate a single layer certificate.
fn validate_layer(layer: &JsonLayerCert, index: usize) -> Result<(), PipelineParseError> {
    if !is_valid_layer_type(&layer.layer_type) {
        return Err(PipelineParseError::InvalidLayerType(
            layer.layer_type.clone(),
        ));
    }

    if layer.input_bounds.is_empty() {
        return Err(PipelineParseError::EmptyBounds { layer: index });
    }
    if layer.output_bounds.is_empty() {
        return Err(PipelineParseError::EmptyBounds { layer: index });
    }

    // Multiplier count must equal 2 * input_dim (box constraints have 2 rows per dim).
    let expected_mult_count = 2 * layer.input_bounds.len();
    if layer.multipliers.len() != expected_mult_count {
        return Err(PipelineParseError::DimensionMismatch {
            layer: index,
            expected: expected_mult_count,
            got: layer.multipliers.len(),
        });
    }

    // Check for negative multipliers.
    for (mi, &m) in layer.multipliers.iter().enumerate() {
        if m < -1e-9 {
            return Err(PipelineParseError::NegativeMultiplier {
                layer: index,
                index: mi,
                value: m,
            });
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Conversion: JsonCertificate -> Vec<ExternalFarkasCert>
// ---------------------------------------------------------------------------

/// Convert a validated [`JsonCertificate`] to a chain of [`ExternalFarkasCert`]s.
///
/// Each layer certificate becomes one Farkas certificate encoding:
///   input in box(layer.input_bounds) => output in box(layer.output_bounds)
///
/// The multipliers from the JSON layer certificate map directly to the
/// Farkas certificate multipliers. Box constraints are generated from the
/// per-dimension interval bounds.
///
/// # Errors
///
/// Returns [`PipelineParseError`] if the certificate fails validation or if
/// dimension invariants are violated during conversion.
#[must_use = "conversion result should be checked for errors"]
pub fn json_to_farkas_chain(
    cert: &JsonCertificate,
) -> Result<Vec<ExternalFarkasCert>, PipelineParseError> {
    validate_certificate(cert)?;

    let mut farkas_certs = Vec::with_capacity(cert.layer_certs.len());

    for (i, layer) in cert.layer_certs.iter().enumerate() {
        let farkas = layer_to_farkas(layer, i)?;
        farkas_certs.push(farkas);
    }

    Ok(farkas_certs)
}

/// Convert a single layer certificate to an [`ExternalFarkasCert`].
fn layer_to_farkas(
    layer: &JsonLayerCert,
    index: usize,
) -> Result<ExternalFarkasCert, PipelineParseError> {
    use super::ibp_crown::Interval;

    let input_dim = layer.input_bounds.len();
    let output_dim = layer.output_bounds.len();

    // Convert bounds to Interval format, then to box constraints.
    let input_intervals: Vec<Interval> = layer
        .input_bounds
        .iter()
        .map(|&(l, u)| Interval::new(l, u))
        .collect();
    let output_intervals: Vec<Interval> = layer
        .output_bounds
        .iter()
        .map(|&(l, u)| Interval::new(l, u))
        .collect();

    let (input_matrix, input_box_bounds) = interval_to_box_constraints(&input_intervals);
    let (output_matrix, output_box_bounds) = interval_to_box_constraints(&output_intervals);

    // Verify multiplier count matches box constraint row count.
    if layer.multipliers.len() != input_matrix.len() {
        return Err(PipelineParseError::DimensionMismatch {
            layer: index,
            expected: input_matrix.len(),
            got: layer.multipliers.len(),
        });
    }

    // For box constraints with equal input/output row counts, input and output
    // must share the same dimension. When they differ (e.g., linear layer
    // maps dim_in -> dim_out), we still use input_dim for both since the
    // Farkas cert encodes constraints in the same variable space.
    // However, box constraints for different-dimensional spaces need matching
    // dimensions for chaining, so we require equal dim here.
    if input_dim != output_dim {
        return Err(PipelineParseError::DimensionMismatch {
            layer: index,
            expected: input_dim,
            got: output_dim,
        });
    }

    Ok(ExternalFarkasCert {
        multipliers: layer.multipliers.clone(),
        input_matrix,
        input_bounds: input_box_bounds,
        output_matrix,
        output_bounds: output_box_bounds,
        input_dim,
        output_dim,
    })
}

/// Compute input bounds from an [`JsonInputSpec`] (center +/- epsilon).
///
/// Returns per-dimension (lower, upper) bounds for L-infinity perturbation.
#[must_use]
pub fn input_spec_to_bounds(spec: &JsonInputSpec) -> Vec<(f64, f64)> {
    spec.center
        .iter()
        .map(|&c| (c - spec.epsilon, c + spec.epsilon))
        .collect()
}

// ---------------------------------------------------------------------------
// Builder helpers (for constructing test certificates)
// ---------------------------------------------------------------------------

/// Build a minimal [`JsonCertificate`] for a network with the given layer
/// certificates. Uses default input spec and output property.
#[cfg(test)]
pub(crate) fn build_test_certificate(
    network_id: &str,
    layer_certs: Vec<JsonLayerCert>,
    input_center: Vec<f64>,
    epsilon: f64,
    true_class: usize,
    margin: f64,
) -> JsonCertificate {
    let num_layers = layer_certs.len();
    JsonCertificate {
        network_id: network_id.to_string(),
        num_layers,
        layer_certs,
        input_spec: JsonInputSpec {
            center: input_center,
            epsilon,
        },
        output_property: JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class,
            margin,
        },
    }
}

/// Build a simple identity-like layer certificate for testing.
///
/// Creates a layer where input and output bounds are the same dimension,
/// with unit multipliers (all 1.0) encoding bound-weakening entailment.
#[cfg(test)]
pub(crate) fn build_identity_layer_cert(
    layer_index: usize,
    layer_type: &str,
    bounds: &[(f64, f64)],
) -> JsonLayerCert {
    let dim = bounds.len();
    JsonLayerCert {
        layer_index,
        layer_type: layer_type.to_string(),
        multipliers: vec![1.0; 2 * dim],
        input_bounds: bounds.to_vec(),
        output_bounds: bounds.to_vec(),
        weight_matrix: None,
        bias: None,
        activation_pattern: None,
    }
}

/// Build a layer certificate with explicit input/output bounds.
#[cfg(test)]
pub(crate) fn build_layer_cert(
    layer_index: usize,
    layer_type: &str,
    input_bounds: &[(f64, f64)],
    output_bounds: &[(f64, f64)],
    multipliers: Vec<f64>,
) -> JsonLayerCert {
    JsonLayerCert {
        layer_index,
        layer_type: layer_type.to_string(),
        multipliers,
        input_bounds: input_bounds.to_vec(),
        output_bounds: output_bounds.to_vec(),
        weight_matrix: None,
        bias: None,
        activation_pattern: None,
    }
}
