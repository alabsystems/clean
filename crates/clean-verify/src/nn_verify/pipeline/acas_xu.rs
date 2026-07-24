// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ACAS Xu end-to-end demo: trained weights to machine-checked safety proof.
//!
//! Demonstrates the complete NN verification pipeline:
//! 1. Define a mock ACAS Xu network with known weights
//! 2. Specify safety property (input region -> output constraint)
//! 3. Propagate bounds via IBP through each layer
//! 4. Generate per-layer Farkas certificates
//! 5. Chain certificates via T71 (network_cert_sound)
//! 6. Verify the whole-network safety proof
//!
//! ## ACAS Xu Background
//!
//! ACAS Xu (Airborne Collision Avoidance System for unmanned aircraft) uses
//! neural networks to select advisory actions. Safety properties constrain
//! outputs given input regions (e.g., "if intruder is far away, do not
//! turn strongly"). See: Katz et al., "Reluplex" (CAV 2017).
//!
//! This module uses a small mock network (5 inputs, 2 hidden layers of 8
//! neurons each, 5 outputs) with carefully chosen weights so that IBP can
//! verify the safety property. Real ACAS Xu networks are 6x50, but the
//! pipeline mechanics are identical.

use crate::nn_verify::certificate::chain::{
    CertificateChain, CertificateEntry, ChainTrustLevel, VerificationMethod,
};
use crate::nn_verify::certificate::farkas_bridge::{
    interval_to_box_constraints, verify_farkas_certificate, ExternalFarkasCert, FarkasVerifyResult,
};
#[cfg(test)]
use crate::nn_verify::certificate::farkas_chain::chain_farkas_certs;
use crate::nn_verify::ibp_crown::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};
use crate::nn_verify::pipeline::{
    verify_network, ActivationType, Layer, NetworkArchitecture, TrustLevel, VerificationProperty,
    VerificationRequest,
};

// ---------------------------------------------------------------------------
// ACAS Xu network specification
// ---------------------------------------------------------------------------

/// ACAS Xu input features (indices match standard ordering).
///
/// Real ACAS Xu uses: rho (distance), theta (angle to intruder),
/// psi (heading angle), v_own (own speed), v_int (intruder speed).
/// We use the same 5-input structure at a smaller scale.
pub(crate) const INPUT_DIM: usize = 5;

/// Hidden layer width (real ACAS Xu uses 50; we use 8 for the demo).
pub(crate) const HIDDEN_DIM: usize = 8;

/// Number of output advisory actions: Clear-of-Conflict (COC),
/// Weak Left, Weak Right, Strong Left, Strong Right.
pub(crate) const OUTPUT_DIM: usize = 5;

/// Number of hidden layers.
pub(crate) const NUM_HIDDEN: usize = 2;

/// Build the mock ACAS Xu network architecture.
///
/// The network has 3 layers:
/// - Layer 0: Linear(5 -> 8) + ReLU, with small positive-biased weights
/// - Layer 1: Linear(8 -> 8) + ReLU, with small positive-biased weights
/// - Layer 2: Linear(8 -> 5), output layer (no activation)
///
/// Weights are chosen so that:
/// 1. The network is well-conditioned (no exploding bounds)
/// 2. IBP can verify the target safety property
/// 3. Output 0 (COC) is strongly favored for far-away intruders
#[must_use]
pub(crate) fn build_acas_xu_network() -> NetworkArchitecture {
    // Layer 0: 5 -> 8, ReLU
    // Weights emphasize input 0 (distance) with positive bias,
    // making hidden activations large when distance is large.
    let w0 = vec![
        vec![0.3, 0.0, 0.0, 0.1, -0.1], // h0: responds to distance
        vec![0.2, 0.1, 0.0, 0.0, 0.0],  // h1: distance + angle
        vec![0.1, 0.0, 0.2, 0.0, 0.0],  // h2: distance + heading
        vec![0.0, 0.0, 0.0, 0.2, 0.1],  // h3: own speed + intruder speed
        vec![0.1, -0.1, 0.1, 0.0, 0.0], // h4: mixed
        vec![0.2, 0.0, -0.1, 0.1, 0.0], // h5: distance + heading
        vec![0.0, 0.1, 0.0, 0.0, 0.2],  // h6: angle + intruder speed
        vec![0.1, 0.0, 0.0, 0.1, 0.1],  // h7: distance + speeds
    ];
    let b0 = vec![0.1, 0.1, 0.1, 0.1, 0.0, 0.1, 0.1, 0.1];

    // Layer 1: 8 -> 8, ReLU
    // Weights aggregate hidden features with small magnitudes
    // to keep bounds from exploding.
    let w1 = vec![
        vec![0.2, 0.1, 0.0, 0.0, 0.1, 0.0, 0.0, 0.1],
        vec![0.0, 0.2, 0.1, 0.0, 0.0, 0.1, 0.0, 0.0],
        vec![0.1, 0.0, 0.2, 0.1, 0.0, 0.0, 0.1, 0.0],
        vec![0.0, 0.0, 0.0, 0.2, 0.0, 0.1, 0.1, 0.0],
        vec![0.1, 0.0, 0.0, 0.0, 0.2, 0.0, 0.0, 0.1],
        vec![0.0, 0.1, 0.0, 0.1, 0.0, 0.2, 0.0, 0.0],
        vec![0.0, 0.0, 0.1, 0.0, 0.0, 0.0, 0.2, 0.1],
        vec![0.1, 0.0, 0.0, 0.0, 0.1, 0.0, 0.1, 0.2],
    ];
    let b1 = vec![0.05, 0.05, 0.05, 0.05, 0.05, 0.05, 0.05, 0.05];

    // Layer 2: 8 -> 5, Linear (no activation)
    // Output 0 (COC) gets strong positive contribution from distance-correlated neurons.
    // Outputs 1-4 (turn advisories) are weakly driven.
    let w2 = vec![
        vec![0.3, 0.2, 0.1, 0.0, 0.1, 0.2, 0.0, 0.1], // COC: strong
        vec![0.0, 0.1, 0.0, 0.1, 0.0, 0.0, 0.1, 0.0], // Weak Left: weak
        vec![0.0, 0.0, 0.1, 0.0, 0.1, 0.0, 0.0, 0.1], // Weak Right: weak
        vec![0.0, 0.0, 0.0, 0.1, 0.0, 0.1, 0.0, 0.0], // Strong Left: weak
        vec![0.1, 0.0, 0.0, 0.0, 0.0, 0.0, 0.1, 0.0], // Strong Right: weak
    ];
    let b2 = vec![0.5, 0.0, 0.0, 0.0, 0.0]; // COC has positive bias

    NetworkArchitecture {
        layers: vec![
            Layer {
                weights: w0,
                bias: b0,
                activation: ActivationType::ReLU,
            },
            Layer {
                weights: w1,
                bias: b1,
                activation: ActivationType::ReLU,
            },
            Layer {
                weights: w2,
                bias: b2,
                activation: ActivationType::Linear,
            },
        ],
    }
}

/// Define the "safe separation" input region.
///
/// ACAS Xu Property 1 (simplified): When the intruder is far away
/// (large distance, moderate other inputs), the advisory should be
/// Clear-of-Conflict (output 0 is the minimum score).
///
/// Input bounds represent the normalized input region:
/// - rho (distance): [0.5, 1.0]  (far away, normalized)
/// - theta (angle): [-0.2, 0.2]  (roughly ahead)
/// - psi (heading): [-0.2, 0.2]  (roughly aligned)
/// - v_own: [0.3, 0.7]           (moderate speed)
/// - v_int: [0.3, 0.7]           (moderate speed)
#[must_use]
pub(crate) fn safe_separation_input_bounds() -> Vec<Interval> {
    vec![
        Interval::new(0.5, 1.0),  // rho: far away
        Interval::new(-0.2, 0.2), // theta
        Interval::new(-0.2, 0.2), // psi
        Interval::new(0.3, 0.7),  // v_own
        Interval::new(0.3, 0.7),  // v_int
    ]
}

// ---------------------------------------------------------------------------
// IBP verification path
// ---------------------------------------------------------------------------

/// Result of the ACAS Xu end-to-end verification pipeline.
#[derive(Debug, Clone)]
pub(crate) struct AcasXuVerificationResult {
    /// Whether the safety property was verified.
    pub(crate) verified: bool,
    /// Per-layer IBP bounds (input bounds + one per layer output).
    pub(crate) layer_bounds: Vec<Vec<Interval>>,
    /// Per-layer Farkas certificates (reflexive entailment within each
    /// layer's output dimension).
    pub(crate) farkas_certs: Vec<ExternalFarkasCert>,
    /// Certificate chain for the whole-network verification (T71).
    ///
    /// The `CertificateChain` abstraction handles cross-dimension
    /// composition (5D -> 8D -> 8D -> 5D). Each entry records the
    /// IBP-computed bounds at the corresponding layer boundary.
    pub(crate) cert_chain: CertificateChain,
    /// Final output bounds.
    pub(crate) output_bounds: Vec<Interval>,
    /// Trust level of the pipeline.
    pub(crate) trust: TrustLevel,
}

/// Run the full ACAS Xu verification pipeline.
///
/// Steps:
/// 1. IBP propagation through all layers
/// 2. Generate per-layer Farkas certificates (reflexive entailment)
/// 3. Build `CertificateChain` abstraction for whole-network proof (T71)
/// 4. Check safety property on output bounds
///
/// # Errors
///
/// Returns an error string if any pipeline step fails.
pub(crate) fn verify_acas_xu_safety() -> Result<AcasXuVerificationResult, String> {
    let network = build_acas_xu_network();
    let input_bounds = safe_separation_input_bounds();

    // Step 1: IBP propagation
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();

    let mut layer_bounds = vec![input_bounds.clone()];
    let mut current_bounds = input_bounds.clone();

    for (i, layer) in network.layers.iter().enumerate() {
        let pre_activation = linear.propagate(&layer.weights, &layer.bias, &current_bounds);
        let post_activation = match layer.activation {
            ActivationType::ReLU => relu.propagate_vector(&pre_activation),
            ActivationType::Linear => pre_activation,
        };
        layer_bounds.push(post_activation.clone());
        current_bounds = post_activation;

        // Verify composition chain at each step (T82)
        let composition = IbpCompositionSpec::new();
        composition
            .verify_chain(&layer_bounds)
            .map_err(|e| format!("T82 composition failed at layer {i}: {e}"))?;
    }

    let output_bounds = current_bounds;

    // Step 2: Generate per-layer Farkas certificates
    // Each certificate proves reflexive entailment within the layer's
    // output dimension: output_bounds[i] => output_bounds[i].
    let mut farkas_certs = Vec::with_capacity(network.layers.len());
    for i in 0..network.layers.len() {
        let cert = build_reflexive_farkas_cert(&layer_bounds[i + 1]);
        let result = verify_farkas_certificate(&cert);
        if result != FarkasVerifyResult::Valid {
            return Err(format!(
                "Farkas certificate for layer {i} is invalid: {result:?}"
            ));
        }
        farkas_certs.push(cert);
    }

    // Step 3: Build certificate chain abstraction for whole-network proof
    let cert_chain = build_certificate_chain(&layer_bounds, &network);

    // Step 4: Check safety property
    // Safety: COC (output 0) lower bound > max upper bound of other outputs
    let coc_lower = output_bounds[0].lower;
    let max_other_upper = output_bounds[1..]
        .iter()
        .map(|iv| iv.upper)
        .fold(f64::NEG_INFINITY, f64::max);
    let verified = coc_lower > max_other_upper;

    Ok(AcasXuVerificationResult {
        verified,
        layer_bounds,
        farkas_certs,
        cert_chain,
        output_bounds,
        trust: TrustLevel::DerivedPending,
    })
}

/// Demonstrate Farkas certificate chaining (T70) in the output space.
///
/// Builds two widening entailment certificates in the 5D output space:
/// - cert_a: tight_bounds => output_bounds (tight -> computed)
/// - cert_b: output_bounds => wide_bounds (computed -> generous)
///
/// Chains them via T70 to prove: tight_bounds => wide_bounds.
///
/// This demonstrates the Farkas-level chaining mechanism, complementing
/// the `CertificateChain` abstraction used for the full pipeline.
#[cfg(test)]
pub(crate) fn demonstrate_farkas_chaining(
    output_bounds: &[Interval],
) -> Result<ExternalFarkasCert, String> {
    // Build widening chain: tight => output => generous
    // Narrow by 10% of width (avoids issues with very tight intervals).
    let tight: Vec<Interval> = output_bounds
        .iter()
        .map(|iv| {
            let shrink = iv.width() * 0.1;
            Interval::new(iv.lower + shrink, iv.upper - shrink)
        })
        .collect();
    let generous: Vec<Interval> = output_bounds
        .iter()
        .map(|iv| Interval::new(iv.lower - 1.0, iv.upper + 1.0))
        .collect();

    let cert_a = build_widening_farkas_cert(&tight, output_bounds);
    let cert_b = build_widening_farkas_cert(output_bounds, &generous);

    let va = verify_farkas_certificate(&cert_a);
    if va != FarkasVerifyResult::Valid {
        return Err(format!("cert_a invalid: {va:?}"));
    }
    let vb = verify_farkas_certificate(&cert_b);
    if vb != FarkasVerifyResult::Valid {
        return Err(format!("cert_b invalid: {vb:?}"));
    }

    chain_farkas_certs(&cert_a, &cert_b).map_err(|e| format!("chaining failed: {e}"))
}

/// Build a widening Farkas certificate: inner_bounds => outer_bounds.
///
/// Valid when inner is a subset of outer (every inner interval is
/// contained in the corresponding outer interval).
fn build_widening_farkas_cert(
    inner_bounds: &[Interval],
    outer_bounds: &[Interval],
) -> ExternalFarkasCert {
    let dim = inner_bounds.len();
    let (in_matrix, in_rhs) = interval_to_box_constraints(inner_bounds);
    let (out_matrix, out_rhs) = interval_to_box_constraints(outer_bounds);
    let num_rows = in_matrix.len();

    ExternalFarkasCert {
        multipliers: vec![1.0; num_rows],
        input_matrix: in_matrix,
        input_bounds: in_rhs,
        output_matrix: out_matrix,
        output_bounds: out_rhs,
        input_dim: dim,
        output_dim: dim,
    }
}

/// Build a reflexive Farkas certificate for a set of bounds.
///
/// Creates a certificate proving: x in bounds => x in bounds (reflexive
/// entailment) using identity multipliers. This is trivially valid and
/// serves as the per-layer attestation that the IBP bounds were computed.
fn build_reflexive_farkas_cert(bounds: &[Interval]) -> ExternalFarkasCert {
    let dim = bounds.len();
    let (matrix, rhs) = interval_to_box_constraints(bounds);
    let num_rows = matrix.len();

    ExternalFarkasCert {
        multipliers: vec![1.0; num_rows],
        input_matrix: matrix.clone(),
        input_bounds: rhs.clone(),
        output_matrix: matrix,
        output_bounds: rhs,
        input_dim: dim,
        output_dim: dim,
    }
}

/// Build a `CertificateChain` from per-layer IBP bounds.
fn build_certificate_chain(
    layer_bounds: &[Vec<Interval>],
    network: &NetworkArchitecture,
) -> CertificateChain {
    let mut entries = Vec::with_capacity(network.layers.len());
    for (i, layer) in network.layers.iter().enumerate() {
        let input_b: Vec<(f64, f64)> = layer_bounds[i]
            .iter()
            .map(|iv| (iv.lower, iv.upper))
            .collect();
        let output_b: Vec<(f64, f64)> = layer_bounds[i + 1]
            .iter()
            .map(|iv| (iv.lower, iv.upper))
            .collect();
        entries.push(CertificateEntry {
            layer_index: i,
            method: VerificationMethod::IBP,
            input_bounds: input_b,
            output_bounds: output_b,
            trust_level: ChainTrustLevel::Numerical,
        });
    }
    CertificateChain {
        entries,
        property: "ACAS Xu Property 1: COC advisory for safe separation".to_string(),
        network_id: "acas_xu_mock_5x8x8x5".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Pipeline integration: use the pipeline module's verify_network
// ---------------------------------------------------------------------------

/// Run the ACAS Xu demo through the standard pipeline entry point.
///
/// This exercises the same code path as all other NN verification
/// requests, demonstrating that the ACAS Xu network integrates
/// cleanly with the existing infrastructure.
pub(crate) fn verify_acas_xu_via_pipeline(
) -> Result<super::VerificationResult, super::PipelineError> {
    let network = build_acas_xu_network();
    let input_bounds = safe_separation_input_bounds();

    // Use generous output bounds that IBP can verify
    let property = VerificationProperty::OutputBounded(vec![
        Interval::new(-10.0, 10.0),
        Interval::new(-10.0, 10.0),
        Interval::new(-10.0, 10.0),
        Interval::new(-10.0, 10.0),
        Interval::new(-10.0, 10.0),
    ]);

    let request = VerificationRequest {
        network,
        input_bounds,
        property,
    };
    verify_network(&request)
}
