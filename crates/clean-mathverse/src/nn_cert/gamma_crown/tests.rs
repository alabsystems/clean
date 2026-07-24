// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the gamma-crown JSON certificate parser.

use super::*;
use crate::types::AxiomProfile;

const SAMPLE_CERT_JSON: &str = r#"{
    "network_name": "mnist_relu_4_256",
    "status": "verified",
    "epsilon": 0.03,
    "norm": "Linf",
    "original_class": 7,
    "network": {
        "input_dim": 784,
        "output_dim": 10,
        "layers": [
            { "type": "dense", "input_dim": 784, "output_dim": 256 },
            { "type": "dense", "input_dim": 256, "output_dim": 256 },
            { "type": "dense", "input_dim": 256, "output_dim": 10 }
        ],
        "activation": "relu"
    },
    "bounds": [
        { "layer": 0, "lower": [-1.0, -0.5], "upper": [2.0, 1.5] },
        { "layer": 1, "lower": [0.0, 0.0], "upper": [3.0, 2.0] }
    ],
    "proof_type": "bound_propagation",
    "neuron_stability": [
        { "layer": 0, "always_active": 100, "always_inactive": 50, "unstable": 106 }
    ]
}"#;

#[test]
fn test_parse_gamma_crown_cert_full() {
    let cert = parse_gamma_crown_cert(SAMPLE_CERT_JSON).expect("should parse valid certificate");

    assert_eq!(cert.network_name, "mnist_relu_4_256");
    assert_eq!(cert.result, VerificationResult::Verified);
    assert_eq!(cert.verifier_tool, VerifierTool::GammaCrown);
    assert_eq!(cert.network_spec.input_dim, 784);
    assert_eq!(cert.network_spec.output_dim, 10);
    assert_eq!(cert.network_spec.layers.len(), 3);
    assert_eq!(cert.network_spec.activation, Activation::ReLU);

    match &cert.property.input_region {
        InputRegion::EpsilonBall {
            epsilon,
            norm,
            center,
        } => {
            assert!((epsilon - 0.03).abs() < f64::EPSILON);
            assert_eq!(*norm, LpNorm::Linf);
            assert!(center.is_empty());
        }
    }

    match &cert.property.output_constraint {
        OutputConstraint::ClassificationPreserved { original_class } => {
            assert_eq!(*original_class, 7);
        }
        _ => panic!("expected ClassificationPreserved"),
    }

    assert_eq!(
        cert.certificate_data.proof_type,
        ProofType::BoundPropagation
    );
    assert_eq!(cert.certificate_data.bounds.len(), 2);
    assert_eq!(cert.certificate_data.intermediate_results.len(), 1);

    let profile = cert.axiom_profile();
    assert!(profile.has(AxiomProfile::FLOAT_APPROX));
    assert!(profile.has(AxiomProfile::NN_ABSTRACTION));
}

#[test]
fn test_parse_gamma_crown_cert_minimal() {
    let json = r#"{
        "status": "verified",
        "network": { "input_dim": 10, "output_dim": 2 }
    }"#;

    let cert = parse_gamma_crown_cert(json).expect("should parse minimal certificate");
    assert_eq!(cert.network_name, "unknown_network");
    assert_eq!(cert.result, VerificationResult::Verified);
    assert_eq!(cert.network_spec.input_dim, 10);
    assert!(cert.network_spec.layers.is_empty());
}

#[test]
fn test_parse_gamma_crown_cert_counterexample() {
    let json = r#"{
        "status": "counterexample",
        "network": { "input_dim": 5, "output_dim": 3 }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    assert_eq!(cert.result, VerificationResult::Counterexample);
}

#[test]
fn test_parse_gamma_crown_cert_unknown_status() {
    let json = r#"{
        "status": "timeout",
        "network": { "input_dim": 5, "output_dim": 3 }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    assert_eq!(cert.result, VerificationResult::Unknown);
}

#[test]
fn test_parse_gamma_crown_cert_missing_status() {
    let json = r#"{ "network": { "input_dim": 5, "output_dim": 3 } }"#;
    let msg = parse_gamma_crown_cert(json).unwrap_err().to_string();
    assert!(msg.contains("missing 'status' field"));
}

#[test]
fn test_parse_gamma_crown_cert_missing_network() {
    let json = r#"{ "status": "verified" }"#;
    let msg = parse_gamma_crown_cert(json).unwrap_err().to_string();
    assert!(msg.contains("missing 'network' field"));
}

#[test]
fn test_parse_gamma_crown_cert_invalid_json() {
    let err = parse_gamma_crown_cert("not json").unwrap_err();
    assert!(matches!(err, MathverseError::Json(_)));
}

#[test]
fn test_parse_gamma_crown_cert_alpha_beta_tool() {
    let json = r#"{
        "status": "verified",
        "tool": "alpha-beta-CROWN",
        "network": { "input_dim": 5, "output_dim": 3 }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    assert_eq!(cert.verifier_tool, VerifierTool::AlphaBetaCrown);
}

#[test]
fn test_parse_gamma_crown_cert_conv_layers() {
    let json = r#"{
        "status": "verified",
        "network": {
            "input_dim": 3072, "output_dim": 10,
            "layers": [
                { "type": "conv2d", "input_dim": 3072, "output_dim": 1024 },
                { "type": "dense", "input_dim": 1024, "output_dim": 10 }
            ]
        }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    assert_eq!(cert.network_spec.layers[0].kind, LayerKind::Conv);
    assert_eq!(cert.network_spec.layers[1].kind, LayerKind::Dense);
}

#[test]
fn test_parse_gamma_crown_cert_l2_norm() {
    let json = r#"{
        "status": "verified", "epsilon": 0.5, "norm": "L2",
        "network": { "input_dim": 10, "output_dim": 2 }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    match &cert.property.input_region {
        InputRegion::EpsilonBall { norm, .. } => assert_eq!(*norm, LpNorm::L2),
    }
}

#[test]
fn test_parse_gamma_crown_cert_milp_proof() {
    let json = r#"{
        "status": "verified", "proof_type": "milp",
        "network": { "input_dim": 5, "output_dim": 2 }
    }"#;
    let cert = parse_gamma_crown_cert(json).expect("parse");
    assert_eq!(cert.certificate_data.proof_type, ProofType::Milp);
}

#[test]
fn test_parse_gamma_crown_certs_array() {
    let json = r#"[
        { "status": "verified", "network": { "input_dim": 10, "output_dim": 2 } },
        { "status": "counterexample", "network": { "input_dim": 20, "output_dim": 5 } }
    ]"#;
    let certs = parse_gamma_crown_certs(json).expect("parse");
    assert_eq!(certs.len(), 2);
    assert_eq!(certs[0].result, VerificationResult::Verified);
    assert_eq!(certs[1].result, VerificationResult::Counterexample);
}

#[test]
fn test_parse_gamma_crown_certs_empty_array() {
    let certs = parse_gamma_crown_certs("[]").expect("parse");
    assert!(certs.is_empty());
}

#[test]
fn test_parse_status_variants() {
    assert_eq!(
        parse_status(Some("safe")).unwrap(),
        VerificationResult::Verified
    );
    assert_eq!(
        parse_status(Some("VERIFIED")).unwrap(),
        VerificationResult::Verified
    );
    assert_eq!(
        parse_status(Some("holds")).unwrap(),
        VerificationResult::Verified
    );
    assert_eq!(
        parse_status(Some("unsafe")).unwrap(),
        VerificationResult::Counterexample
    );
    assert_eq!(
        parse_status(Some("violated")).unwrap(),
        VerificationResult::Counterexample
    );
    assert_eq!(
        parse_status(Some("inconclusive")).unwrap(),
        VerificationResult::Unknown
    );
    assert!(parse_status(Some("garbage")).is_err());
    assert!(parse_status(None).is_err());
}
