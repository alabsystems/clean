// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! gamma-crown JSON certificate parser.
//!
//! Parses the JSON output from gamma-crown (and alpha-beta-CROWN) verification
//! runs into [`NNVerificationCert`] instances. The parser is lenient: missing
//! optional fields produce sensible defaults rather than errors.
//!
//! ## gamma-crown JSON format (expected structure)
//!
//! ```json
//! {
//!   "network_name": "mnist_relu_4_256",
//!   "status": "verified",
//!   "epsilon": 0.03,
//!   "norm": "Linf",
//!   "original_class": 7,
//!   "network": {
//!     "input_dim": 784,
//!     "output_dim": 10,
//!     "layers": [
//!       { "type": "dense", "input_dim": 784, "output_dim": 256 },
//!       { "type": "dense", "input_dim": 256, "output_dim": 10 }
//!     ],
//!     "activation": "relu"
//!   },
//!   "bounds": [
//!     { "layer": 0, "lower": [...], "upper": [...] }
//!   ],
//!   "proof_type": "bound_propagation",
//!   "neuron_stability": [
//!     { "layer": 0, "always_active": 100, "always_inactive": 50, "unstable": 106 }
//!   ]
//! }
//! ```

use serde::Deserialize;

use crate::error::{MathverseError, MathverseResult};

use super::types::{
    Activation, CertificateData, InputRegion, IntermediateResult, LayerBounds, LayerKind,
    LayerSpec, LpNorm, NNVerificationCert, NetworkSpec, OutputConstraint, ProofType,
    RobustnessProperty, VerificationResult, VerifierTool,
};

pub mod experiments;

pub use experiments::{
    parse_phase1_artifact, C002Summary, C004Summary, Conjecture, ExperimentConfig,
    ExperimentResult, Phase1Artifact,
};

// ---------------------------------------------------------------------------
// Raw JSON schema (serde intermediate representation)
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct RawGammaCrownCert {
    #[serde(default)]
    network_name: Option<String>,

    #[serde(default)]
    status: Option<String>,

    #[serde(default)]
    epsilon: Option<f64>,

    #[serde(default)]
    norm: Option<String>,

    #[serde(default)]
    original_class: Option<usize>,

    #[serde(default)]
    network: Option<RawNetwork>,

    #[serde(default)]
    bounds: Option<Vec<RawLayerBounds>>,

    #[serde(default)]
    proof_type: Option<String>,

    #[serde(default)]
    neuron_stability: Option<Vec<RawNeuronStability>>,

    /// Tool identifier. If absent, defaults to gamma-crown.
    #[serde(default)]
    tool: Option<String>,
}

#[derive(Deserialize)]
struct RawNetwork {
    #[serde(default)]
    input_dim: Option<usize>,

    #[serde(default)]
    output_dim: Option<usize>,

    #[serde(default)]
    layers: Option<Vec<RawLayer>>,

    #[serde(default)]
    activation: Option<String>,
}

#[derive(Deserialize)]
struct RawLayer {
    #[serde(rename = "type", default)]
    kind: Option<String>,

    #[serde(default)]
    input_dim: Option<usize>,

    #[serde(default)]
    output_dim: Option<usize>,
}

#[derive(Deserialize)]
struct RawLayerBounds {
    #[serde(default)]
    layer: Option<usize>,

    #[serde(default)]
    lower: Option<Vec<f64>>,

    #[serde(default)]
    upper: Option<Vec<f64>>,
}

#[derive(Deserialize)]
struct RawNeuronStability {
    #[serde(default)]
    layer: Option<usize>,

    #[serde(default)]
    always_active: Option<usize>,

    #[serde(default)]
    always_inactive: Option<usize>,

    #[serde(default)]
    unstable: Option<usize>,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse a gamma-crown JSON certificate string into an [`NNVerificationCert`].
///
/// # Errors
///
/// Returns `MathverseError::Json` if the JSON is malformed, or
/// `MathverseError::ImportFailed` if required fields are missing.
pub fn parse_gamma_crown_cert(json: &str) -> MathverseResult<NNVerificationCert> {
    let raw: RawGammaCrownCert = serde_json::from_str(json).map_err(MathverseError::Json)?;

    let network_name = raw
        .network_name
        .unwrap_or_else(|| "unknown_network".to_string());

    let result = parse_status(raw.status.as_deref())?;
    let verifier_tool = parse_tool(raw.tool.as_deref());
    let network_spec = parse_network(raw.network.as_ref())?;
    let property = parse_property(raw.epsilon, raw.norm.as_deref(), raw.original_class);
    let certificate_data = parse_certificate_data(
        raw.proof_type.as_deref(),
        raw.bounds.as_deref(),
        raw.neuron_stability.as_deref(),
    );

    Ok(NNVerificationCert {
        network_name,
        property,
        verifier_tool,
        result,
        certificate_data,
        network_spec,
    })
}

/// Parse multiple gamma-crown certificates from a JSON array string.
///
/// # Errors
///
/// Returns an error if the JSON is not a valid array or any certificate fails.
pub fn parse_gamma_crown_certs(json: &str) -> MathverseResult<Vec<NNVerificationCert>> {
    let raw_array: Vec<serde_json::Value> =
        serde_json::from_str(json).map_err(MathverseError::Json)?;

    raw_array
        .iter()
        .enumerate()
        .map(|(i, val)| {
            let cert_json = val.to_string();
            parse_gamma_crown_cert(&cert_json)
                .map_err(|e| e.with_context(&format!("certificate index {i}")))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Internal parsing helpers
// ---------------------------------------------------------------------------

fn parse_status(status: Option<&str>) -> MathverseResult<VerificationResult> {
    match status {
        Some(s) => {
            let lower = s.to_lowercase();
            // Check counterexample/unsafe BEFORE verified/safe to avoid
            // "unsafe" matching the "safe" substring.
            if lower.contains("counterexample")
                || lower.contains("violated")
                || lower.contains("unsafe")
                || lower == "sat"
            {
                Ok(VerificationResult::Counterexample)
            } else if lower.contains("unknown")
                || lower.contains("timeout")
                || lower.contains("inconclusive")
            {
                Ok(VerificationResult::Unknown)
            } else if lower.contains("verified") || lower.contains("safe") || lower == "holds" {
                Ok(VerificationResult::Verified)
            } else {
                Err(MathverseError::ImportFailed {
                    system: "gamma-crown".to_string(),
                    reason: format!("unrecognized status: {s}"),
                })
            }
        }
        None => Err(MathverseError::ImportFailed {
            system: "gamma-crown".to_string(),
            reason: "missing 'status' field".to_string(),
        }),
    }
}

fn parse_tool(tool: Option<&str>) -> VerifierTool {
    match tool {
        Some(t) => {
            let lower = t.to_lowercase();
            if lower.contains("alpha") || lower.contains("ab-crown") {
                VerifierTool::AlphaBetaCrown
            } else if lower.contains("vnn") {
                VerifierTool::VnnComp
            } else {
                VerifierTool::GammaCrown
            }
        }
        None => VerifierTool::GammaCrown,
    }
}

fn parse_network(raw: Option<&RawNetwork>) -> MathverseResult<NetworkSpec> {
    let net = raw.ok_or_else(|| MathverseError::ImportFailed {
        system: "gamma-crown".to_string(),
        reason: "missing 'network' field".to_string(),
    })?;

    let input_dim = net.input_dim.unwrap_or(0);
    let output_dim = net.output_dim.unwrap_or(0);

    let layers = net
        .layers
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .map(|l| LayerSpec {
            kind: parse_layer_kind(l.kind.as_deref()),
            input_dim: l.input_dim.unwrap_or(0),
            output_dim: l.output_dim.unwrap_or(0),
        })
        .collect();

    let activation = parse_activation(net.activation.as_deref());

    Ok(NetworkSpec {
        input_dim,
        output_dim,
        layers,
        activation,
    })
}

fn parse_layer_kind(kind: Option<&str>) -> LayerKind {
    match kind {
        Some(k) => {
            let lower = k.to_lowercase();
            if lower.contains("conv") {
                LayerKind::Conv
            } else if lower.contains("resid") || lower.contains("skip") {
                LayerKind::Residual
            } else if lower.contains("layernorm") || lower == "ln" {
                LayerKind::LayerNorm
            } else if lower.contains("batchnorm") || lower == "bn" {
                LayerKind::BatchNorm
            } else {
                LayerKind::Dense
            }
        }
        None => LayerKind::Dense,
    }
}

fn parse_activation(activation: Option<&str>) -> Activation {
    match activation {
        Some(a) => {
            let lower = a.to_lowercase();
            if lower.contains("relu") {
                Activation::ReLU
            } else if lower.contains("sigmoid") {
                Activation::Sigmoid
            } else if lower.contains("tanh") {
                Activation::Tanh
            } else {
                Activation::None
            }
        }
        None => Activation::ReLU, // most common in NN verification
    }
}

fn parse_property(
    epsilon: Option<f64>,
    norm: Option<&str>,
    original_class: Option<usize>,
) -> RobustnessProperty {
    let eps = epsilon.unwrap_or(0.0);
    let lp_norm = match norm {
        Some(n) => {
            let lower = n.to_lowercase();
            if lower.contains("inf") {
                LpNorm::Linf
            } else if lower.contains("2") {
                LpNorm::L2
            } else if lower.contains("1") {
                LpNorm::L1
            } else {
                LpNorm::Linf
            }
        }
        None => LpNorm::Linf,
    };

    let input_region = InputRegion::EpsilonBall {
        epsilon: eps,
        norm: lp_norm,
        center: vec![],
    };

    let output_constraint = match original_class {
        Some(cls) => OutputConstraint::ClassificationPreserved {
            original_class: cls,
        },
        None => OutputConstraint::ClassificationPreserved { original_class: 0 },
    };

    RobustnessProperty {
        input_region,
        output_constraint,
    }
}

fn parse_certificate_data(
    proof_type: Option<&str>,
    bounds: Option<&[RawLayerBounds]>,
    stability: Option<&[RawNeuronStability]>,
) -> CertificateData {
    let pt = match proof_type {
        Some(p) => {
            let lower = p.to_lowercase();
            // Check MILP before LP to avoid "milp" matching "lp" substring.
            if lower.contains("milp") || lower.contains("mip") {
                ProofType::Milp
            } else if lower.contains("lp") || lower.contains("dual") {
                ProofType::LpDuality
            } else if lower.contains("sdp") {
                ProofType::Sdp
            } else if lower.contains("abstract") || lower.contains("interval") {
                ProofType::AbstractInterpretation
            } else {
                ProofType::BoundPropagation
            }
        }
        None => ProofType::BoundPropagation,
    };

    let layer_bounds: Vec<LayerBounds> = bounds
        .unwrap_or(&[])
        .iter()
        .map(|b| LayerBounds {
            layer_idx: b.layer.unwrap_or(0),
            lower: b.lower.clone().unwrap_or_default(),
            upper: b.upper.clone().unwrap_or_default(),
        })
        .collect();

    let intermediate_results: Vec<IntermediateResult> = stability
        .unwrap_or(&[])
        .iter()
        .map(|s| IntermediateResult::NeuronStability {
            layer_idx: s.layer.unwrap_or(0),
            always_active: s.always_active.unwrap_or(0),
            always_inactive: s.always_inactive.unwrap_or(0),
            unstable: s.unstable.unwrap_or(0),
        })
        .collect();

    CertificateData {
        proof_type: pt,
        bounds: layer_bounds,
        intermediate_results,
    }
}

#[cfg(test)]
mod tests;
