// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end neural network verification pipeline (IBP layer).
//!
//! Connects IBP bound propagation with certificate chain composition to
//! verify properties of multi-layer networks. Given a network architecture,
//! input bounds, and a property to verify, the pipeline:
//!
//! 1. Propagates interval bounds through each layer (IBP linear + activation)
//! 2. Builds a per-layer proof chain recording each bound computation
//! 3. Composes the chain and checks whether output bounds satisfy the property
//!
//! This is the integration layer between [`super::ibp_crown`] specs and
//! end-to-end verification queries from gamma-crown.
//!
//! ## Relationship to `certificate::pipeline`
//!
//! The [`certificate::pipeline`](super::certificate::pipeline) module handles
//! JSON-encoded entailment certificates. This module works at the IBP
//! computation level: it takes weight matrices and input bounds, runs IBP
//! propagation, and produces a proof chain with trust classification.

pub(crate) mod acas_xu;
pub mod diagnostics;
#[cfg(test)]
mod tests_acas_xu;
#[cfg(test)]
mod tests_diagnostics;

use super::ibp_crown::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Activation function applied after a linear layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ActivationType {
    /// Identity (no activation).
    Linear,
    /// Rectified linear unit: max(0, x).
    ReLU,
}

/// A single layer: affine transform y = Wx + b followed by an activation.
#[derive(Debug, Clone)]
pub struct Layer {
    /// Weight matrix in row-major order (output_dim x input_dim).
    pub weights: Vec<Vec<f64>>,
    /// Bias vector (length = output_dim).
    pub bias: Vec<f64>,
    /// Activation applied after the affine transform.
    pub activation: ActivationType,
}

/// Full network architecture as a sequence of layers.
#[derive(Debug, Clone)]
pub struct NetworkArchitecture {
    /// Ordered layers from input to output.
    pub layers: Vec<Layer>,
}

/// Property to verify about network outputs.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum VerificationProperty {
    /// Every output dimension lies within the given bounds.
    OutputBounded(Vec<Interval>),
}

/// A verification request: network + input region + desired property.
#[derive(Debug, Clone)]
pub struct VerificationRequest {
    /// Network to verify.
    pub network: NetworkArchitecture,
    /// Element-wise bounds on each input dimension.
    pub input_bounds: Vec<Interval>,
    /// Property that the output must satisfy.
    pub property: VerificationProperty,
}

/// One entry in the proof chain: the bounds computed for a single layer.
#[derive(Debug, Clone)]
pub struct LayerCertificate {
    /// Layer index (0-based).
    pub layer_index: usize,
    /// Bounds after the affine transform (before activation).
    pub pre_activation_bounds: Vec<Interval>,
    /// Bounds after the activation function.
    pub post_activation_bounds: Vec<Interval>,
}

/// Trust profile classifying how much of the proof was fully derived.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustLevel {
    /// All steps rely on DerivedPending specs (sound but axiom-dependent).
    DerivedPending,
}

/// Result of a successful verification.
#[derive(Debug, Clone)]
pub struct VerificationResult {
    /// Whether the property was verified.
    pub verified: bool,
    /// Per-layer certificate chain.
    pub chain: Vec<LayerCertificate>,
    /// Final output bounds computed by the pipeline.
    pub output_bounds: Vec<Interval>,
    /// Trust classification for the proof.
    pub trust: TrustLevel,
}

/// Errors from the IBP verification pipeline.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PipelineError {
    /// Dimension mismatch between adjacent layers.
    #[error("dimension mismatch at layer {layer}: expected input dim {expected}, got {actual}")]
    DimensionMismatch {
        layer: usize,
        expected: usize,
        actual: usize,
    },

    /// Input bounds length does not match the first layer's input dimension.
    #[error("input bounds length {bounds_len} does not match first layer input dim {input_dim}")]
    InputBoundsMismatch { bounds_len: usize, input_dim: usize },

    /// A layer has inconsistent weight/bias dimensions.
    #[error("layer {layer}: bias length {bias_len} != weight rows {weight_rows}")]
    LayerShapeMismatch {
        layer: usize,
        bias_len: usize,
        weight_rows: usize,
    },

    /// The network has no layers.
    #[error("network has no layers")]
    EmptyNetwork,

    /// The IBP composition chain failed validation.
    #[error("chain validation failed: {reason}")]
    ChainValidation { reason: String },

    /// Property bound length does not match output dimension.
    #[error("property bound length {prop_len} does not match output dim {output_dim}")]
    PropertyDimensionMismatch { prop_len: usize, output_dim: usize },
}

// ---------------------------------------------------------------------------
// Pipeline entry point
// ---------------------------------------------------------------------------

/// Run end-to-end IBP verification on a neural network.
///
/// Propagates interval bounds layer-by-layer using T80 (IBP linear), T81
/// (IBP ReLU), and T82 (IBP composition), builds a certificate chain, and
/// checks the final output bounds against the requested property.
///
/// # Errors
///
/// Returns [`PipelineError`] on dimension mismatches, empty networks, or
/// chain validation failures.
pub fn verify_network(request: &VerificationRequest) -> Result<VerificationResult, PipelineError> {
    let network = &request.network;
    if network.layers.is_empty() {
        return Err(PipelineError::EmptyNetwork);
    }

    // Validate first layer input dimension.
    let first_input_dim = first_layer_input_dim(&network.layers[0]);
    if request.input_bounds.len() != first_input_dim {
        return Err(PipelineError::InputBoundsMismatch {
            bounds_len: request.input_bounds.len(),
            input_dim: first_input_dim,
        });
    }

    validate_network_shapes(network)?;

    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let composition = IbpCompositionSpec::new();

    let mut current_bounds = request.input_bounds.clone();
    let mut chain = Vec::with_capacity(network.layers.len());
    let mut all_layer_bounds = Vec::with_capacity(network.layers.len() + 1);
    all_layer_bounds.push(current_bounds.clone());

    for (i, layer) in network.layers.iter().enumerate() {
        let pre_activation = linear.propagate(&layer.weights, &layer.bias, &current_bounds);

        let post_activation = match layer.activation {
            ActivationType::Linear => pre_activation.clone(),
            ActivationType::ReLU => relu.propagate_vector(&pre_activation),
        };

        chain.push(LayerCertificate {
            layer_index: i,
            pre_activation_bounds: pre_activation,
            post_activation_bounds: post_activation.clone(),
        });

        all_layer_bounds.push(post_activation.clone());
        current_bounds = post_activation;
    }

    composition
        .verify_chain(&all_layer_bounds)
        .map_err(|reason| PipelineError::ChainValidation { reason })?;

    let verified = check_property(&request.property, &current_bounds)?;

    Ok(VerificationResult {
        verified,
        chain,
        output_bounds: current_bounds,
        trust: TrustLevel::DerivedPending,
    })
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn first_layer_input_dim(layer: &Layer) -> usize {
    if layer.weights.is_empty() {
        0
    } else {
        layer.weights[0].len()
    }
}

/// Validate that all layers have consistent weight/bias shapes and adjacent
/// layers have matching dimensions.
fn validate_network_shapes(network: &NetworkArchitecture) -> Result<(), PipelineError> {
    for (i, layer) in network.layers.iter().enumerate() {
        let output_dim = layer.weights.len();
        if layer.bias.len() != output_dim {
            return Err(PipelineError::LayerShapeMismatch {
                layer: i,
                bias_len: layer.bias.len(),
                weight_rows: output_dim,
            });
        }

        // Check that all rows have the same width.
        if output_dim > 0 {
            let input_dim = layer.weights[0].len();
            for row in &layer.weights[1..] {
                if row.len() != input_dim {
                    return Err(PipelineError::LayerShapeMismatch {
                        layer: i,
                        bias_len: row.len(),
                        weight_rows: input_dim,
                    });
                }
            }
        }

        // Check inter-layer dimension match.
        if i > 0 {
            let prev_output_dim = network.layers[i - 1].weights.len();
            let this_input_dim = first_layer_input_dim(layer);
            if this_input_dim != prev_output_dim {
                return Err(PipelineError::DimensionMismatch {
                    layer: i,
                    expected: prev_output_dim,
                    actual: this_input_dim,
                });
            }
        }
    }
    Ok(())
}

/// Check whether computed output bounds satisfy the requested property.
fn check_property(
    property: &VerificationProperty,
    output_bounds: &[Interval],
) -> Result<bool, PipelineError> {
    match property {
        VerificationProperty::OutputBounded(expected) => {
            if expected.len() != output_bounds.len() {
                return Err(PipelineError::PropertyDimensionMismatch {
                    prop_len: expected.len(),
                    output_dim: output_bounds.len(),
                });
            }
            Ok(output_bounds
                .iter()
                .zip(expected.iter())
                .all(|(actual, bound)| actual.is_subset_of(bound)))
        }
    }
}

/// Compute the actual network output for a concrete input vector.
///
/// Used in tests to spot-check that IBP bounds contain actual outputs.
#[cfg(test)]
pub(crate) fn evaluate_network(network: &NetworkArchitecture, input: &[f64]) -> Vec<f64> {
    let mut current = input.to_vec();
    for layer in &network.layers {
        let mut next = Vec::with_capacity(layer.weights.len());
        for (row, b) in layer.weights.iter().zip(layer.bias.iter()) {
            let val: f64 = row
                .iter()
                .zip(current.iter())
                .map(|(w, x)| w * x)
                .sum::<f64>()
                + b;
            next.push(val);
        }
        current = match layer.activation {
            ActivationType::Linear => next,
            ActivationType::ReLU => next.into_iter().map(|v| v.max(0.0)).collect(),
        };
    }
    current
}
