// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON string parser for gamma-crown Farkas certificates.
//!
//! Deserializes JSON-encoded neural network verification certificates from
//! gamma-crown into the internal [`JsonCertificate`] type, then converts
//! to the [`ExternalFarkasCert`] chain for Farkas verification.
//!
//! ## JSON Schema
//!
//! ```json
//! {
//!   "network_id": "mnist_relu_3x100",
//!   "num_layers": 2,
//!   "layer_certs": [
//!     {
//!       "layer_index": 0,
//!       "layer_type": "linear",
//!       "multipliers": [1.0, 1.0, 1.0, 1.0],
//!       "input_bounds": [[-1.0, 1.0], [-1.0, 1.0]],
//!       "output_bounds": [[-2.0, 2.0], [-2.0, 2.0]]
//!     }
//!   ],
//!   "input_spec": { "center": [0.0, 0.0], "epsilon": 1.0 },
//!   "output_property": {
//!     "property_type": "robust_classification",
//!     "true_class": 0,
//!     "margin": 0.5
//!   }
//! }
//! ```
//!
//! ## Design
//!
//! Uses serde_json for deserialization into intermediate serde types, then
//! converts to the existing [`JsonCertificate`] types. This avoids adding
//! `Serialize`/`Deserialize` derives to the existing non_exhaustive types
//! which would be a breaking API change.

use super::e2e_json_parser::{
    JsonCertificate, JsonInputSpec, JsonLayerCert, JsonOutputProperty, PipelineParseError,
};
use serde::Deserialize;

// ---------------------------------------------------------------------------
// Serde intermediate types
// ---------------------------------------------------------------------------

/// Serde-deserializable certificate (mirrors [`JsonCertificate`]).
#[derive(Debug, Deserialize)]
struct RawCertificate {
    network_id: String,
    num_layers: usize,
    layer_certs: Vec<RawLayerCert>,
    input_spec: RawInputSpec,
    output_property: RawOutputProperty,
}

/// Serde-deserializable layer certificate (mirrors [`JsonLayerCert`]).
#[derive(Debug, Deserialize)]
struct RawLayerCert {
    layer_index: usize,
    layer_type: String,
    multipliers: Vec<f64>,
    /// Per-dimension bounds as `[[lower, upper], ...]`.
    input_bounds: Vec<[f64; 2]>,
    /// Per-dimension bounds as `[[lower, upper], ...]`.
    output_bounds: Vec<[f64; 2]>,
    #[serde(default)]
    weight_matrix: Option<Vec<Vec<f64>>>,
    #[serde(default)]
    bias: Option<Vec<f64>>,
    /// Per-neuron activation status for ReLU layers: `"stable_active"`,
    /// `"stable_inactive"`, or `"unstable"`. Empty for non-ReLU layers.
    #[serde(default)]
    activation_pattern: Option<Vec<String>>,
}

/// Serde-deserializable input specification (mirrors [`JsonInputSpec`]).
#[derive(Debug, Deserialize)]
struct RawInputSpec {
    center: Vec<f64>,
    epsilon: f64,
}

/// Serde-deserializable output property (mirrors [`JsonOutputProperty`]).
#[derive(Debug, Deserialize)]
struct RawOutputProperty {
    property_type: String,
    true_class: usize,
    margin: f64,
}

// ---------------------------------------------------------------------------
// Conversion: Raw -> JsonCertificate
// ---------------------------------------------------------------------------

/// Convert a deserialized raw certificate to a [`JsonCertificate`].
fn raw_to_json_certificate(raw: RawCertificate) -> JsonCertificate {
    let layer_certs = raw
        .layer_certs
        .into_iter()
        .map(raw_to_json_layer_cert)
        .collect();

    JsonCertificate {
        network_id: raw.network_id,
        num_layers: raw.num_layers,
        layer_certs,
        input_spec: JsonInputSpec {
            center: raw.input_spec.center,
            epsilon: raw.input_spec.epsilon,
        },
        output_property: JsonOutputProperty {
            property_type: raw.output_property.property_type,
            true_class: raw.output_property.true_class,
            margin: raw.output_property.margin,
        },
    }
}

/// Convert a raw layer certificate to a [`JsonLayerCert`].
fn raw_to_json_layer_cert(raw: RawLayerCert) -> JsonLayerCert {
    let input_bounds = raw.input_bounds.iter().map(|b| (b[0], b[1])).collect();
    let output_bounds = raw.output_bounds.iter().map(|b| (b[0], b[1])).collect();

    JsonLayerCert {
        layer_index: raw.layer_index,
        layer_type: raw.layer_type,
        multipliers: raw.multipliers,
        input_bounds,
        output_bounds,
        weight_matrix: raw.weight_matrix,
        bias: raw.bias,
        activation_pattern: raw.activation_pattern,
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse a JSON string into a [`JsonCertificate`].
///
/// Deserializes the JSON and converts bounds from `[[lower, upper], ...]`
/// array format to `(f64, f64)` tuple format used by the internal types.
///
/// # Errors
///
/// Returns [`PipelineParseError::InvalidJson`] if the JSON is malformed or
/// does not match the expected schema.
pub fn parse_certificate_json(json: &str) -> Result<JsonCertificate, PipelineParseError> {
    let raw: RawCertificate =
        serde_json::from_str(json).map_err(|e| PipelineParseError::InvalidJson(e.to_string()))?;
    Ok(raw_to_json_certificate(raw))
}

/// Parse a JSON string and convert directly to a Farkas certificate chain.
///
/// Combines [`parse_certificate_json`] with
/// [`super::e2e_json_parser::json_to_farkas_chain`] for a single-step
/// JSON-to-Farkas conversion.
///
/// # Errors
///
/// Returns [`PipelineParseError`] for JSON parse errors or certificate
/// validation failures.
pub fn parse_json_to_farkas_chain(
    json: &str,
) -> Result<
    (
        JsonCertificate,
        Vec<super::certificate::farkas_bridge::ExternalFarkasCert>,
    ),
    PipelineParseError,
> {
    let cert = parse_certificate_json(json)?;
    let chain = super::e2e_json_parser::json_to_farkas_chain(&cert)?;
    Ok((cert, chain))
}

// ---------------------------------------------------------------------------
// Full pipeline: JSON -> Verify -> Expr
// ---------------------------------------------------------------------------

/// Error from the full JSON-to-Expr pipeline.
#[derive(Debug)]
#[non_exhaustive]
pub enum CertPipelineError {
    /// JSON parsing or certificate validation failed.
    Parse(PipelineParseError),
    /// Farkas certificate verification failed (at least one layer invalid).
    VerificationFailed {
        /// Number of layers that passed verification.
        passed: usize,
        /// Total number of layers.
        total: usize,
    },
    /// Expr building failed for one of the Farkas certificates.
    ExprBuild(super::cert_expr_builder::CertExprError),
}

impl std::fmt::Display for CertPipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Parse(e) => write!(f, "parse error: {e}"),
            Self::VerificationFailed { passed, total } => {
                write!(f, "verification failed: {passed}/{total} layers passed")
            }
            Self::ExprBuild(e) => write!(f, "expr build error: {e}"),
        }
    }
}

impl std::error::Error for CertPipelineError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Parse(e) => Some(e),
            Self::VerificationFailed { .. } => None,
            Self::ExprBuild(e) => Some(e),
        }
    }
}

impl From<PipelineParseError> for CertPipelineError {
    fn from(e: PipelineParseError) -> Self {
        Self::Parse(e)
    }
}

impl From<super::cert_expr_builder::CertExprError> for CertPipelineError {
    fn from(e: super::cert_expr_builder::CertExprError) -> Self {
        Self::ExprBuild(e)
    }
}

/// Result of the full JSON-to-Expr pipeline.
#[derive(Debug)]
pub struct CertPipelineResult {
    /// The parsed certificate.
    pub certificate: JsonCertificate,
    /// Per-layer Expr proof terms (one per verified Farkas certificate).
    pub layer_exprs: Vec<super::cert_expr_builder::FarkasCertExpr>,
    /// Per-layer Farkas certificates.
    pub farkas_chain: Vec<super::certificate::farkas_bridge::ExternalFarkasCert>,
    /// Whether the full verification pipeline passed.
    pub verified: bool,
}

/// Run the full JSON-to-Expr pipeline: parse, validate, verify, build Exprs.
///
/// This is the primary entry point for converting gamma-crown JSON certificates
/// into clean kernel `Expr` proof terms. The pipeline:
///
/// 1. Parses the JSON string into a [`JsonCertificate`]
/// 2. Converts to a Farkas certificate chain
/// 3. Verifies each layer's Farkas certificate
/// 4. Builds clean `Expr` proof terms for each verified certificate
///
/// # Errors
///
/// Returns [`CertPipelineError`] if parsing, verification, or Expr building fails.
#[must_use = "pipeline result should be inspected"]
pub fn json_to_expr_pipeline(json: &str) -> Result<CertPipelineResult, CertPipelineError> {
    use super::certificate::farkas_bridge::{verify_farkas_certificate, FarkasVerifyResult};

    // Step 1-2: Parse and convert to Farkas chain.
    let (certificate, farkas_chain) = parse_json_to_farkas_chain(json)?;

    // Step 3: Verify each layer's Farkas certificate.
    let mut passed = 0;
    for farkas in &farkas_chain {
        if verify_farkas_certificate(farkas) == FarkasVerifyResult::Valid {
            passed += 1;
        }
    }
    if passed != farkas_chain.len() {
        return Err(CertPipelineError::VerificationFailed {
            passed,
            total: farkas_chain.len(),
        });
    }

    // Step 4: Build Expr proof terms for each verified Farkas certificate.
    let mut layer_exprs = Vec::with_capacity(farkas_chain.len());
    for farkas in &farkas_chain {
        let expr = super::cert_expr_builder::farkas_cert_to_expr(farkas)?;
        layer_exprs.push(expr);
    }

    Ok(CertPipelineResult {
        certificate,
        layer_exprs,
        farkas_chain,
        verified: true,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
