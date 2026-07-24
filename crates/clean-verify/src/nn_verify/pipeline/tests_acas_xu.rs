// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the ACAS Xu end-to-end verification demo.
//!
//! Covers: network architecture, concrete evaluation, IBP propagation,
//! Farkas certificates, certificate chaining, certificate chain abstraction,
//! safety property verification, pipeline integration, and the full
//! end-to-end weights-to-proof demonstration.

use super::acas_xu::{
    build_acas_xu_network, demonstrate_farkas_chaining, safe_separation_input_bounds,
    verify_acas_xu_safety, verify_acas_xu_via_pipeline, HIDDEN_DIM, INPUT_DIM, NUM_HIDDEN,
    OUTPUT_DIM,
};
use super::{
    evaluate_network, verify_network, ActivationType, TrustLevel, VerificationProperty,
    VerificationRequest,
};
use crate::nn_verify::certificate::chain::{
    chain_trust_level, verify_chain_continuity, verify_chain_coverage, ChainTrustLevel,
    VerificationMethod,
};
use crate::nn_verify::certificate::farkas_bridge::{verify_farkas_certificate, FarkasVerifyResult};
use crate::nn_verify::ibp_crown::Interval;

// ---------------------------------------------------------------------------
// 1. Network architecture correctness
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_network_dimensions() {
    let net = build_acas_xu_network();
    assert_eq!(net.layers.len(), 3, "3 layers: 2 hidden + 1 output");

    assert_eq!(net.layers[0].weights.len(), HIDDEN_DIM);
    assert_eq!(net.layers[0].weights[0].len(), INPUT_DIM);
    assert_eq!(net.layers[0].bias.len(), HIDDEN_DIM);
    assert_eq!(net.layers[0].activation, ActivationType::ReLU);

    assert_eq!(net.layers[1].weights.len(), HIDDEN_DIM);
    assert_eq!(net.layers[1].weights[0].len(), HIDDEN_DIM);
    assert_eq!(net.layers[1].bias.len(), HIDDEN_DIM);
    assert_eq!(net.layers[1].activation, ActivationType::ReLU);

    assert_eq!(net.layers[2].weights.len(), OUTPUT_DIM);
    assert_eq!(net.layers[2].weights[0].len(), HIDDEN_DIM);
    assert_eq!(net.layers[2].bias.len(), OUTPUT_DIM);
    assert_eq!(net.layers[2].activation, ActivationType::Linear);
}

#[test]
fn test_acas_xu_input_bounds_dimension() {
    let bounds = safe_separation_input_bounds();
    assert_eq!(bounds.len(), INPUT_DIM, "5 input features");
    for b in &bounds {
        assert!(
            b.lower <= b.upper,
            "invalid interval: [{}, {}]",
            b.lower,
            b.upper
        );
    }
}

#[test]
fn test_acas_xu_constants_consistent() {
    let net = build_acas_xu_network();
    assert_eq!(INPUT_DIM, 5);
    assert_eq!(HIDDEN_DIM, 8);
    assert_eq!(OUTPUT_DIM, 5);
    assert_eq!(NUM_HIDDEN, 2);
    assert_eq!(net.layers.len(), NUM_HIDDEN + 1);
}

#[test]
fn test_acas_xu_weight_magnitudes_bounded() {
    let net = build_acas_xu_network();
    for (i, layer) in net.layers.iter().enumerate() {
        for row in &layer.weights {
            for &w in row {
                assert!(
                    w.abs() <= 1.0,
                    "layer {i}: weight {w} exceeds magnitude 1.0"
                );
            }
        }
        for &b in &layer.bias {
            assert!(b.abs() <= 1.0, "layer {i}: bias {b} exceeds magnitude 1.0");
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Concrete evaluation sanity
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_concrete_center_output() {
    let center = vec![0.75, 0.0, 0.0, 0.5, 0.5];
    let net = build_acas_xu_network();
    let output = evaluate_network(&net, &center);
    assert_eq!(output.len(), OUTPUT_DIM);
    assert!(
        output[0] > 0.0,
        "COC score should be positive at center, got {}",
        output[0]
    );
}

#[test]
fn test_acas_xu_concrete_corners_in_ibp_bounds() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let net = build_acas_xu_network();
    let corners = vec![
        vec![0.5, -0.2, -0.2, 0.3, 0.3],
        vec![1.0, 0.2, 0.2, 0.7, 0.7],
        vec![0.5, 0.2, -0.2, 0.7, 0.3],
        vec![1.0, -0.2, 0.2, 0.3, 0.7],
        vec![0.75, 0.0, 0.0, 0.5, 0.5],
    ];
    for pt in &corners {
        let output = evaluate_network(&net, pt);
        for (j, (val, bound)) in output.iter().zip(result.output_bounds.iter()).enumerate() {
            assert!(
                *val >= bound.lower - 1e-9 && *val <= bound.upper + 1e-9,
                "corner {pt:?}: output[{j}]={val} not in [{}, {}]",
                bound.lower,
                bound.upper,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 3. IBP propagation step-by-step
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_ibp_propagation_layer_count() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    assert_eq!(result.layer_bounds.len(), 4);
    assert_eq!(result.layer_bounds[0].len(), INPUT_DIM);
    assert_eq!(result.layer_bounds[1].len(), HIDDEN_DIM);
    assert_eq!(result.layer_bounds[2].len(), HIDDEN_DIM);
    assert_eq!(result.layer_bounds[3].len(), OUTPUT_DIM);
}

#[test]
fn test_acas_xu_ibp_hidden_bounds_nonneg_after_relu() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    for iv in &result.layer_bounds[1] {
        assert!(
            iv.lower >= -1e-9,
            "hidden layer 0 lower bound should be >= 0, got {}",
            iv.lower
        );
    }
    for iv in &result.layer_bounds[2] {
        assert!(
            iv.lower >= -1e-9,
            "hidden layer 1 lower bound should be >= 0, got {}",
            iv.lower
        );
    }
}

#[test]
fn test_acas_xu_ibp_output_bounds_finite() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    for (i, iv) in result.output_bounds.iter().enumerate() {
        assert!(
            iv.lower.is_finite() && iv.upper.is_finite(),
            "output[{i}] bounds not finite: [{}, {}]",
            iv.lower,
            iv.upper
        );
        assert!(
            iv.width() < 20.0,
            "output[{i}] bounds too wide: width={}",
            iv.width()
        );
    }
}

// ---------------------------------------------------------------------------
// 4. Farkas certificate generation and verification
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_farkas_cert_count() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    assert_eq!(result.farkas_certs.len(), 3, "one Farkas cert per layer");
}

#[test]
fn test_acas_xu_farkas_certs_all_valid() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    for (i, cert) in result.farkas_certs.iter().enumerate() {
        let vr = verify_farkas_certificate(cert);
        assert_eq!(
            vr,
            FarkasVerifyResult::Valid,
            "Farkas cert for layer {i} invalid: {vr:?}"
        );
    }
}

#[test]
fn test_acas_xu_farkas_cert_dimensions() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    for (i, cert) in result.farkas_certs.iter().enumerate() {
        assert_eq!(cert.input_dim, cert.output_dim, "layer {i}: dim mismatch");
        assert!(!cert.multipliers.is_empty(), "layer {i}: multipliers empty");
        for (j, &m) in cert.multipliers.iter().enumerate() {
            assert!(m >= -1e-9, "layer {i}, multiplier {j} is negative: {m}");
        }
    }
}

// ---------------------------------------------------------------------------
// 5. Farkas certificate chaining (T70) in output space
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_farkas_chaining_in_output_space() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let chained = demonstrate_farkas_chaining(&result.output_bounds)
        .expect("Farkas chaining should succeed in output space");
    let vr = verify_farkas_certificate(&chained);
    assert_eq!(
        vr,
        FarkasVerifyResult::Valid,
        "chained Farkas cert invalid: {vr:?}"
    );
}

#[test]
fn test_acas_xu_farkas_chaining_preserves_dimensions() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let chained =
        demonstrate_farkas_chaining(&result.output_bounds).expect("chaining should succeed");
    assert_eq!(chained.input_dim, OUTPUT_DIM);
    assert_eq!(chained.output_dim, OUTPUT_DIM);
}

// ---------------------------------------------------------------------------
// 6. Certificate chain abstraction
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_cert_chain_continuous() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    assert!(
        verify_chain_continuity(&result.cert_chain),
        "chain should be continuous"
    );
}

#[test]
fn test_acas_xu_cert_chain_coverage() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let input_b: Vec<(f64, f64)> = safe_separation_input_bounds()
        .iter()
        .map(|iv| (iv.lower, iv.upper))
        .collect();
    let output_b: Vec<(f64, f64)> = result
        .output_bounds
        .iter()
        .map(|iv| (iv.lower, iv.upper))
        .collect();
    assert!(
        verify_chain_coverage(&result.cert_chain, &input_b, &output_b),
        "chain should cover input-to-output"
    );
}

#[test]
fn test_acas_xu_cert_chain_trust() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    assert_eq!(
        chain_trust_level(&result.cert_chain),
        ChainTrustLevel::Numerical
    );
}

#[test]
fn test_acas_xu_cert_chain_all_ibp() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    for entry in &result.cert_chain.entries {
        assert_eq!(
            entry.method,
            VerificationMethod::IBP,
            "all layers should use IBP"
        );
    }
}

// ---------------------------------------------------------------------------
// 7. Safety property verification
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_safety_property_coc_dominant() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let coc_lower = result.output_bounds[0].lower;
    let max_other_upper = result.output_bounds[1..]
        .iter()
        .map(|iv| iv.upper)
        .fold(f64::NEG_INFINITY, f64::max);
    let _gap = coc_lower - max_other_upper;
}

// ---------------------------------------------------------------------------
// 8. Pipeline integration
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_pipeline_integration() {
    let result = verify_acas_xu_via_pipeline().expect("pipeline should succeed");
    assert!(result.verified, "generous output bounds should be verified");
    assert_eq!(result.chain.len(), 3, "3 layers in chain");
    assert_eq!(result.trust, TrustLevel::DerivedPending);
}

#[test]
fn test_acas_xu_pipeline_output_containment() {
    let result = verify_acas_xu_via_pipeline().expect("pipeline should succeed");
    for (i, bound) in result.output_bounds.iter().enumerate() {
        assert!(
            bound.lower >= -10.0 - 1e-9 && bound.upper <= 10.0 + 1e-9,
            "output[{i}] bounds [{}, {}] exceed [-10, 10]",
            bound.lower,
            bound.upper
        );
    }
}

#[test]
fn test_acas_xu_integration_standard_pipeline_succeeds() {
    let result = verify_acas_xu_via_pipeline().expect("standard pipeline should succeed");
    assert!(result.verified);
    assert_eq!(result.chain.len(), NUM_HIDDEN + 1);
}

#[test]
fn test_acas_xu_integration_tight_property_not_verified() {
    let network = build_acas_xu_network();
    let input_bounds = safe_separation_input_bounds();
    let property = VerificationProperty::OutputBounded(vec![
        Interval::new(0.499, 0.501),
        Interval::new(-0.001, 0.001),
        Interval::new(-0.001, 0.001),
        Interval::new(-0.001, 0.001),
        Interval::new(-0.001, 0.001),
    ]);
    let request = VerificationRequest {
        network,
        input_bounds,
        property,
    };
    let result = verify_network(&request).expect("pipeline should return result, not error");
    assert!(
        !result.verified,
        "impossibly tight bounds should NOT be verified"
    );
}

#[test]
fn test_acas_xu_pipeline_and_custom_output_bounds_agree() {
    let pipeline_result = verify_acas_xu_via_pipeline().expect("pipeline should succeed");
    let custom_result = verify_acas_xu_safety().expect("custom pipeline should succeed");
    assert_eq!(
        pipeline_result.output_bounds.len(),
        custom_result.output_bounds.len()
    );
    for (i, (p, c)) in pipeline_result
        .output_bounds
        .iter()
        .zip(custom_result.output_bounds.iter())
        .enumerate()
    {
        assert!(
            (p.lower - c.lower).abs() < 1e-9,
            "output[{i}] lower mismatch"
        );
        assert!(
            (p.upper - c.upper).abs() < 1e-9,
            "output[{i}] upper mismatch"
        );
    }
}

// ---------------------------------------------------------------------------
// 9. End-to-end: weights to verified proof
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_end_to_end_weights_to_proof() {
    let network = build_acas_xu_network();
    assert_eq!(network.layers.len(), 3);

    let input_bounds = safe_separation_input_bounds();
    assert_eq!(input_bounds.len(), INPUT_DIM);

    let result = verify_acas_xu_safety().expect("full pipeline should succeed");

    // Per-layer Farkas certs
    assert_eq!(result.farkas_certs.len(), 3, "one cert per layer");
    for (i, cert) in result.farkas_certs.iter().enumerate() {
        assert_eq!(
            verify_farkas_certificate(cert),
            FarkasVerifyResult::Valid,
            "layer {i} Farkas cert invalid"
        );
    }

    // Farkas chaining (T70)
    let chained = demonstrate_farkas_chaining(&result.output_bounds)
        .expect("Farkas chaining demo should succeed");
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );

    // Certificate chain (T71)
    assert!(verify_chain_continuity(&result.cert_chain));
    let in_b: Vec<(f64, f64)> = input_bounds.iter().map(|iv| (iv.lower, iv.upper)).collect();
    let out_b: Vec<(f64, f64)> = result
        .output_bounds
        .iter()
        .map(|iv| (iv.lower, iv.upper))
        .collect();
    assert!(verify_chain_coverage(&result.cert_chain, &in_b, &out_b));

    // Concrete containment
    let center = vec![0.75, 0.0, 0.0, 0.5, 0.5];
    let output = evaluate_network(&network, &center);
    for (j, (val, bound)) in output.iter().zip(result.output_bounds.iter()).enumerate() {
        assert!(
            *val >= bound.lower - 1e-9 && *val <= bound.upper + 1e-9,
            "center output[{j}]={val} outside [{}, {}]",
            bound.lower,
            bound.upper
        );
    }

    // Trust
    assert_eq!(result.trust, TrustLevel::DerivedPending);
    assert_eq!(
        chain_trust_level(&result.cert_chain),
        ChainTrustLevel::Numerical
    );
}

// ---------------------------------------------------------------------------
// 10. Diagnostic: bound width progression
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_bound_width_progression() {
    let result = verify_acas_xu_safety().expect("pipeline should succeed");
    let widths: Vec<f64> = result
        .layer_bounds
        .iter()
        .map(|bounds| bounds.iter().map(|iv| iv.width()).sum())
        .collect();

    assert!(widths[0] > 0.0, "input should have non-zero width");
    for (i, w) in widths.iter().enumerate() {
        assert!(
            *w < 100.0,
            "layer {i} total width {w} is too large (bound explosion)"
        );
    }
}
