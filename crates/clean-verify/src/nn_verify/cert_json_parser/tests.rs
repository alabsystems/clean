// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for cert_json_parser: JSON deserialization + full pipeline.

use super::super::certificate::farkas_bridge::{verify_farkas_certificate, FarkasVerifyResult};
use super::super::e2e_json_parser::PipelineParseError;
use super::*;

/// Minimal 2-variable, 1-layer Farkas certificate JSON.
const SIMPLE_2VAR_JSON: &str = r#"{
    "network_id": "test_simple",
    "num_layers": 1,
    "layer_certs": [
        {
            "layer_index": 0,
            "layer_type": "linear",
            "multipliers": [1.0, 1.0, 1.0, 1.0],
            "input_bounds": [[-1.0, 1.0], [-2.0, 2.0]],
            "output_bounds": [[-1.0, 1.0], [-2.0, 2.0]]
        }
    ],
    "input_spec": { "center": [0.0, 0.0], "epsilon": 1.0 },
    "output_property": {
        "property_type": "robust_classification",
        "true_class": 0,
        "margin": 0.0
    }
}"#;

/// Multi-constraint certificate: 3-layer, 2-variable, widening bounds.
const MULTI_CONSTRAINT_JSON: &str = r#"{
    "network_id": "test_multi",
    "num_layers": 3,
    "layer_certs": [
        {
            "layer_index": 0,
            "layer_type": "linear",
            "multipliers": [1.0, 1.0, 1.0, 1.0],
            "input_bounds": [[-1.0, 1.0], [-1.0, 1.0]],
            "output_bounds": [[-1.5, 1.5], [-1.5, 1.5]]
        },
        {
            "layer_index": 1,
            "layer_type": "relu",
            "multipliers": [1.0, 1.0, 1.0, 1.0],
            "input_bounds": [[-1.5, 1.5], [-1.5, 1.5]],
            "output_bounds": [[-2.0, 2.0], [-2.0, 2.0]]
        },
        {
            "layer_index": 2,
            "layer_type": "linear",
            "multipliers": [1.0, 1.0, 1.0, 1.0],
            "input_bounds": [[-2.0, 2.0], [-2.0, 2.0]],
            "output_bounds": [[-2.0, 2.0], [-2.0, 2.0]]
        }
    ],
    "input_spec": { "center": [0.0, 0.0], "epsilon": 1.0 },
    "output_property": {
        "property_type": "robust_classification",
        "true_class": 0,
        "margin": 0.0
    }
}"#;

/// Edge case: single variable.
const SINGLE_VAR_JSON: &str = r#"{
    "network_id": "test_single_var",
    "num_layers": 1,
    "layer_certs": [
        {
            "layer_index": 0,
            "layer_type": "relu",
            "multipliers": [1.0, 1.0],
            "input_bounds": [[0.0, 1.0]],
            "output_bounds": [[0.0, 1.0]]
        }
    ],
    "input_spec": { "center": [0.5], "epsilon": 0.5 },
    "output_property": {
        "property_type": "robust_classification",
        "true_class": 0,
        "margin": 0.0
    }
}"#;

// -----------------------------------------------------------------------
// JSON parsing tests
// -----------------------------------------------------------------------

#[test]
fn test_parse_simple_2var_certificate() {
    let cert =
        parse_certificate_json(SIMPLE_2VAR_JSON).expect("should parse simple 2-var certificate");
    assert_eq!(cert.network_id, "test_simple");
    assert_eq!(cert.num_layers, 1);
    assert_eq!(cert.layer_certs.len(), 1);

    let layer = &cert.layer_certs[0];
    assert_eq!(layer.layer_index, 0);
    assert_eq!(layer.layer_type, "linear");
    assert_eq!(layer.multipliers, vec![1.0, 1.0, 1.0, 1.0]);
    assert_eq!(layer.input_bounds, vec![(-1.0, 1.0), (-2.0, 2.0)]);
    assert_eq!(layer.output_bounds, vec![(-1.0, 1.0), (-2.0, 2.0)]);
    assert_eq!(cert.input_spec.center, vec![0.0, 0.0]);
    assert_eq!(cert.input_spec.epsilon, 1.0);
}

#[test]
fn test_parse_multi_constraint_certificate() {
    let cert = parse_certificate_json(MULTI_CONSTRAINT_JSON)
        .expect("should parse multi-constraint certificate");
    assert_eq!(cert.num_layers, 3);
    assert_eq!(cert.layer_certs.len(), 3);
    assert_eq!(cert.layer_certs[0].layer_type, "linear");
    assert_eq!(cert.layer_certs[1].layer_type, "relu");
    assert_eq!(cert.layer_certs[2].layer_type, "linear");

    assert_eq!(cert.layer_certs[0].input_bounds[0], (-1.0, 1.0));
    assert_eq!(cert.layer_certs[0].output_bounds[0], (-1.5, 1.5));
    assert_eq!(cert.layer_certs[1].input_bounds[0], (-1.5, 1.5));
    assert_eq!(cert.layer_certs[2].output_bounds[0], (-2.0, 2.0));
}

#[test]
fn test_parse_single_var_certificate() {
    let cert =
        parse_certificate_json(SINGLE_VAR_JSON).expect("should parse single-var certificate");
    assert_eq!(cert.num_layers, 1);
    assert_eq!(cert.layer_certs[0].input_bounds.len(), 1);
    assert_eq!(cert.layer_certs[0].input_bounds[0], (0.0, 1.0));
    assert_eq!(cert.input_spec.center, vec![0.5]);
}

#[test]
fn test_parse_to_farkas_chain_simple() {
    let (cert, chain) = parse_json_to_farkas_chain(SIMPLE_2VAR_JSON)
        .expect("should parse and convert to Farkas chain");
    assert_eq!(cert.network_id, "test_simple");
    assert_eq!(chain.len(), 1);
    assert_eq!(chain[0].input_dim, 2);
    assert_eq!(chain[0].output_dim, 2);
    assert_eq!(
        verify_farkas_certificate(&chain[0]),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_parse_to_farkas_chain_multi_layer() {
    let (_cert, chain) = parse_json_to_farkas_chain(MULTI_CONSTRAINT_JSON)
        .expect("should parse multi-layer to Farkas chain");
    assert_eq!(chain.len(), 3);
    for (i, farkas) in chain.iter().enumerate() {
        assert_eq!(
            verify_farkas_certificate(farkas),
            FarkasVerifyResult::Valid,
            "layer {i}"
        );
    }
}

#[test]
fn test_parse_to_farkas_chain_single_var() {
    let (_cert, chain) = parse_json_to_farkas_chain(SINGLE_VAR_JSON)
        .expect("should parse single-var to Farkas chain");
    assert_eq!(chain.len(), 1);
    assert_eq!(chain[0].input_dim, 1);
}

#[test]
fn test_parse_invalid_json_returns_error() {
    let result = parse_certificate_json("not valid json");
    match result {
        Err(PipelineParseError::InvalidJson(_)) => {}
        other => panic!("expected InvalidJson, got {other:?}"),
    }
}

#[test]
fn test_parse_missing_field_returns_error() {
    let json = r#"{ "network_id": "test" }"#;
    match parse_certificate_json(json) {
        Err(PipelineParseError::InvalidJson(msg)) => {
            assert!(msg.contains("missing field"), "error: {msg}");
        }
        other => panic!("expected InvalidJson, got {other:?}"),
    }
}

#[test]
fn test_parse_with_optional_weight_matrix() {
    let json = r#"{
        "network_id": "test_weights",
        "num_layers": 1,
        "layer_certs": [{
            "layer_index": 0, "layer_type": "linear",
            "multipliers": [1.0, 1.0],
            "input_bounds": [[0.0, 1.0]], "output_bounds": [[0.0, 1.0]],
            "weight_matrix": [[1.0]], "bias": [0.0]
        }],
        "input_spec": { "center": [0.5], "epsilon": 0.5 },
        "output_property": {
            "property_type": "robust_classification",
            "true_class": 0, "margin": 0.0
        }
    }"#;
    let cert = parse_certificate_json(json).expect("should parse");
    assert_eq!(
        cert.layer_certs[0].weight_matrix.as_ref().unwrap(),
        &vec![vec![1.0]]
    );
    assert_eq!(cert.layer_certs[0].bias.as_ref().unwrap(), &vec![0.0]);
}

// -----------------------------------------------------------------------
// Activation pattern tests
// -----------------------------------------------------------------------

#[test]
fn test_parse_with_activation_pattern() {
    let json = r#"{
        "network_id": "test_relu_pattern",
        "num_layers": 1,
        "layer_certs": [{
            "layer_index": 0, "layer_type": "relu",
            "multipliers": [1.0, 1.0, 1.0, 1.0],
            "input_bounds": [[-1.0, 1.0], [0.5, 2.0]],
            "output_bounds": [[-1.0, 1.0], [0.5, 2.0]],
            "activation_pattern": ["unstable", "stable_active"]
        }],
        "input_spec": { "center": [0.0, 1.25], "epsilon": 1.0 },
        "output_property": {
            "property_type": "robust_classification",
            "true_class": 0, "margin": 0.0
        }
    }"#;
    let cert = parse_certificate_json(json).expect("should parse");
    let pattern = cert.layer_certs[0]
        .activation_pattern
        .as_ref()
        .expect("should have activation_pattern");
    assert_eq!(pattern, &["unstable", "stable_active"]);
}

#[test]
fn test_parse_activation_pattern_absent_is_none() {
    let cert = parse_certificate_json(SIMPLE_2VAR_JSON).expect("should parse");
    assert!(cert.layer_certs[0].activation_pattern.is_none());
}

// -----------------------------------------------------------------------
// Full pipeline tests: JSON -> Verify -> Expr
// -----------------------------------------------------------------------

#[test]
fn test_json_to_expr_pipeline_simple() {
    let result = json_to_expr_pipeline(SIMPLE_2VAR_JSON).expect("simple pipeline should succeed");
    assert!(result.verified);
    assert_eq!(result.certificate.network_id, "test_simple");
    assert_eq!(result.farkas_chain.len(), 1);
    assert_eq!(result.layer_exprs.len(), 1);

    let expr = &result.layer_exprs[0];
    assert_eq!(expr.input_dim, 2);
    assert_eq!(expr.output_dim, 2);
    assert!(expr.prop_type.is_pi(), "prop_type should be Pi (forall)");
    assert!(expr.proof_term.is_lam(), "proof_term should be Lambda");
}

#[test]
fn test_json_to_expr_pipeline_multi_layer() {
    let result =
        json_to_expr_pipeline(MULTI_CONSTRAINT_JSON).expect("multi-layer pipeline should succeed");
    assert!(result.verified);
    assert_eq!(result.farkas_chain.len(), 3);
    assert_eq!(result.layer_exprs.len(), 3);

    for (i, expr) in result.layer_exprs.iter().enumerate() {
        assert!(expr.prop_type.is_pi(), "layer {i}: prop_type should be Pi");
        assert!(
            expr.proof_term.is_lam(),
            "layer {i}: proof_term should be Lambda"
        );
        assert_eq!(expr.input_dim, 2, "layer {i}: input_dim should be 2");
    }
}

#[test]
fn test_json_to_expr_pipeline_single_var() {
    let result =
        json_to_expr_pipeline(SINGLE_VAR_JSON).expect("single-var pipeline should succeed");
    assert!(result.verified);
    assert_eq!(result.layer_exprs.len(), 1);
    assert_eq!(result.layer_exprs[0].input_dim, 1);
}

#[test]
fn test_json_to_expr_pipeline_invalid_json() {
    match json_to_expr_pipeline("not json") {
        Err(CertPipelineError::Parse(PipelineParseError::InvalidJson(_))) => {}
        other => panic!("expected Parse(InvalidJson), got {other:?}"),
    }
}

#[test]
fn test_json_to_expr_pipeline_negative_multiplier() {
    let json = r#"{
        "network_id": "test_neg_mult",
        "num_layers": 1,
        "layer_certs": [{
            "layer_index": 0, "layer_type": "linear",
            "multipliers": [-1.0, 1.0],
            "input_bounds": [[0.0, 1.0]], "output_bounds": [[0.0, 1.0]]
        }],
        "input_spec": { "center": [0.5], "epsilon": 0.5 },
        "output_property": {
            "property_type": "robust_classification",
            "true_class": 0, "margin": 0.0
        }
    }"#;
    assert!(json_to_expr_pipeline(json).is_err());
}

/// Realistic gamma-crown certificate: 2-layer MNIST-like network with
/// weight matrix, bias, and activation pattern.
#[test]
fn test_json_to_expr_pipeline_realistic_cert() {
    let json = r#"{
        "network_id": "mnist_2x2_demo",
        "num_layers": 2,
        "layer_certs": [
            {
                "layer_index": 0,
                "layer_type": "linear",
                "multipliers": [1.0, 1.0, 1.0, 1.0],
                "input_bounds": [[-0.5, 0.5], [-0.3, 0.3]],
                "output_bounds": [[-0.5, 0.5], [-0.3, 0.3]],
                "weight_matrix": [[1.0, 0.0], [0.0, 1.0]],
                "bias": [0.0, 0.0]
            },
            {
                "layer_index": 1,
                "layer_type": "relu",
                "multipliers": [1.0, 1.0, 1.0, 1.0],
                "input_bounds": [[-0.5, 0.5], [-0.3, 0.3]],
                "output_bounds": [[-0.5, 0.5], [-0.3, 0.3]],
                "activation_pattern": ["unstable", "unstable"]
            }
        ],
        "input_spec": { "center": [0.0, 0.0], "epsilon": 0.5 },
        "output_property": {
            "property_type": "robust_classification",
            "true_class": 0,
            "margin": 0.0
        }
    }"#;
    let result = json_to_expr_pipeline(json).expect("realistic cert should succeed");
    assert!(result.verified);
    assert_eq!(result.layer_exprs.len(), 2);

    // Layer 0: linear with weight matrix.
    assert!(result.certificate.layer_certs[0].weight_matrix.is_some());
    assert!(result.certificate.layer_certs[0].bias.is_some());

    // Layer 1: relu with activation pattern.
    let pattern = result.certificate.layer_certs[1]
        .activation_pattern
        .as_ref()
        .expect("relu layer should have activation_pattern");
    assert_eq!(pattern, &["unstable", "unstable"]);

    // Both layers produce valid Expr proof terms.
    for (i, expr) in result.layer_exprs.iter().enumerate() {
        assert!(expr.prop_type.is_pi(), "layer {i}: Pi type");
        assert!(expr.proof_term.is_lam(), "layer {i}: Lambda proof");
    }
}

/// Verify generated Expr structure has correct shape (Pi type, Lambda proof).
#[test]
fn test_json_to_expr_pipeline_expr_structure() {
    let result = json_to_expr_pipeline(SIMPLE_2VAR_JSON).expect("should succeed");
    let expr = &result.layer_exprs[0];

    assert!(expr.prop_type.is_pi());
    assert!(expr.proof_term.is_lam());
    assert_eq!(expr.num_input_constraints, 4); // 2 dims * 2 box rows
    assert_eq!(expr.num_output_constraints, 4);
}
