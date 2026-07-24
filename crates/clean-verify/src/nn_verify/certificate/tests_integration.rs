// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for gamma-crown certificate verify + compose pipeline.
//!
//! Loads real JSON fixtures from `tests/fixtures/external_certificates/`,
//! verifies each independently, composes sequential block certificates,
//! and validates the composed result. Also covers error paths: corrupt
//! JSON, dimension mismatches, and invalid coefficients.

use super::composition::{build_simple_entailment, compose_entailment_certs, CompositionError};
use super::farkas_bridge::{
    box_constraints_to_interval, build_simple_box_cert, farkas_to_interval,
    interval_to_box_constraints, verify_farkas_certificate as verify_farkas_bridge,
    ExternalFarkasCert, FarkasBridgeError, FarkasVerifyResult,
};
use super::farkas_chain::chain_farkas_certs;
use super::pipeline::{verify_and_compose_pipeline, PipelineError};
use crate::nn_verify::ibp_crown::Interval;
use clean_elab::cert::external::{
    verify_entailment_certificate, verify_farkas_certificate, ConstraintKind, ExternalCertificate,
    ExternalEntailmentCert, ExternalLinearConstraint, ExternalRational,
};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Fixture helpers
// ---------------------------------------------------------------------------

fn fixture_path(name: &str) -> std::path::PathBuf {
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    workspace_root
        .join("tests/fixtures/external_certificates")
        .join(name)
}

fn load_fixture(name: &str) -> String {
    std::fs::read_to_string(fixture_path(name))
        .unwrap_or_else(|e| panic!("fixture {name} should exist: {e}"))
}

// ---------------------------------------------------------------------------
// 1. Load and verify existing gamma-crown fixtures independently
// ---------------------------------------------------------------------------

#[test]
fn test_fixture_farkas_verifies() {
    let json = load_fixture("gamma_crown_farkas_valid.json");
    let cert: ExternalCertificate =
        serde_json::from_str(&json).expect("farkas fixture should parse");
    match cert {
        ExternalCertificate::Farkas(farkas) => {
            let residual =
                verify_farkas_certificate(&farkas).expect("farkas fixture should verify");
            assert!(
                residual.is_negative(),
                "valid contradiction needs negative residual, got {residual}"
            );
        }
        other => panic!("expected Farkas, got {other:?}"),
    }
}

#[test]
fn test_fixture_entailment_verifies() {
    let json = load_fixture("gamma_crown_entailment_valid.json");
    let cert: ExternalCertificate =
        serde_json::from_str(&json).expect("entailment fixture should parse");
    match cert {
        ExternalCertificate::Entailment(ent) => {
            let (derived, claimed) =
                verify_entailment_certificate(&ent).expect("entailment fixture should verify");
            assert!(
                derived <= claimed,
                "entailment: derived {derived} should be <= claimed {claimed}"
            );
        }
        other => panic!("expected Entailment, got {other:?}"),
    }
}

#[test]
fn test_fixture_batch_all_verify() {
    let json = load_fixture("gamma_crown_batch_valid.json");
    let certs: Vec<ExternalCertificate> = serde_json::from_str(&json).expect("batch should parse");
    assert_eq!(certs.len(), 2);

    for (i, cert) in certs.iter().enumerate() {
        match cert {
            ExternalCertificate::Farkas(f) => {
                verify_farkas_certificate(f)
                    .unwrap_or_else(|e| panic!("batch[{i}] Farkas should verify: {e}"));
            }
            ExternalCertificate::Entailment(e) => {
                verify_entailment_certificate(e)
                    .unwrap_or_else(|e| panic!("batch[{i}] Entailment should verify: {e}"));
            }
            ExternalCertificate::Alethe(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Load and verify NN block fixtures
// ---------------------------------------------------------------------------

#[test]
fn test_nn_block1_linear_verifies() {
    let json = load_fixture("nn_verify_test_block1_linear.json");
    let cert: ExternalEntailmentCert =
        serde_json::from_str(&json).expect("block1 fixture should parse");
    let (derived, claimed) = verify_entailment_certificate(&cert).expect("block1 should verify");
    assert!(derived <= claimed);
}

#[test]
fn test_nn_block2_relu_verifies() {
    let json = load_fixture("nn_verify_test_block2_relu.json");
    let cert: ExternalEntailmentCert =
        serde_json::from_str(&json).expect("block2 fixture should parse");
    let (derived, claimed) = verify_entailment_certificate(&cert).expect("block2 should verify");
    assert!(derived <= claimed);
}

// ---------------------------------------------------------------------------
// 3. Compose sequential block certificates
// ---------------------------------------------------------------------------

#[test]
fn test_compose_nn_block_fixtures() {
    let json1 = load_fixture("nn_verify_test_block1_linear.json");
    let json2 = load_fixture("nn_verify_test_block2_relu.json");

    let cert1: ExternalEntailmentCert = serde_json::from_str(&json1).expect("block1 parse");
    let cert2: ExternalEntailmentCert = serde_json::from_str(&json2).expect("block2 parse");

    let composed =
        compose_entailment_certs(&cert1, &cert2).expect("block1 -> block2 should compose");

    // Block1 conclusion (x0+x1 <= 8) matches block2 premise.
    assert_eq!(composed.replaced_premise_index, 0);
    assert_eq!(composed.spliced_premise_count, 1);

    // Composed cert: x0+x1 <= 7 implies x0+x1 <= 10.
    assert_eq!(
        composed.certificate.conclusion.constant,
        ExternalRational::from_int(10)
    );
    assert_eq!(composed.certificate.premises.len(), 1);
    assert_eq!(
        composed.certificate.premises[0].constant,
        ExternalRational::from_int(7)
    );
}

#[test]
fn test_compose_verifies_composed_result() {
    let json1 = load_fixture("nn_verify_test_block1_linear.json");
    let json2 = load_fixture("nn_verify_test_block2_relu.json");

    let cert1: ExternalEntailmentCert = serde_json::from_str(&json1).unwrap();
    let cert2: ExternalEntailmentCert = serde_json::from_str(&json2).unwrap();

    let composed = compose_entailment_certs(&cert1, &cert2).unwrap();

    // The composed certificate should independently verify.
    let (derived, claimed) = verify_entailment_certificate(&composed.certificate)
        .expect("composed certificate must verify independently");
    assert!(derived <= claimed);
}

// ---------------------------------------------------------------------------
// 4. Full pipeline: parse JSON -> verify -> compose -> verify composed
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_two_block_chain() {
    let json1 = load_fixture("nn_verify_test_block1_linear.json");
    let json2 = load_fixture("nn_verify_test_block2_relu.json");

    let result =
        verify_and_compose_pipeline(&[&json1, &json2]).expect("two-block pipeline should succeed");

    assert_eq!(result.input_count, 2);
    assert_eq!(result.composition_steps, 1);
    assert_eq!(
        result.certificate.conclusion.constant,
        ExternalRational::from_int(10)
    );
}

#[test]
fn test_pipeline_single_fixture() {
    let json = load_fixture("gamma_crown_entailment_valid.json");
    let result =
        verify_and_compose_pipeline(&[&json]).expect("single-cert pipeline should succeed");
    assert_eq!(result.input_count, 1);
    assert_eq!(result.composition_steps, 0);
}

#[test]
fn test_pipeline_three_block_chain() {
    // Build a 3-block chain using synthetic certs:
    // cert_a: x <= 3 implies x <= 5
    // cert_b: x <= 5 implies x <= 7
    // cert_c: x <= 7 implies x <= 10
    let a = build_simple_entailment("x", 1, 3, 5);
    let b = build_simple_entailment("x", 1, 5, 7);
    let c = build_simple_entailment("x", 1, 7, 10);

    let json_a = serde_json::to_string(&a).unwrap();
    let json_b = serde_json::to_string(&b).unwrap();
    let json_c = serde_json::to_string(&c).unwrap();

    let result = verify_and_compose_pipeline(&[&json_a, &json_b, &json_c])
        .expect("3-block pipeline should succeed");

    assert_eq!(result.input_count, 3);
    assert_eq!(result.composition_steps, 2);
    // Final: x <= 3 implies x <= 10
    assert_eq!(
        result.certificate.conclusion.constant,
        ExternalRational::from_int(10)
    );
}

// ---------------------------------------------------------------------------
// 5. Error cases: corrupt JSON
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_corrupt_json_first() {
    let result = verify_and_compose_pipeline(&["{ not json !!!"]);
    match result {
        Err(PipelineError::ParseError { index: 0, .. }) => {}
        other => panic!("expected ParseError at index 0, got {other:?}"),
    }
}

#[test]
fn test_pipeline_corrupt_json_second() {
    let good = load_fixture("gamma_crown_entailment_valid.json");
    let result = verify_and_compose_pipeline(&[&good, "{ broken"]);
    match result {
        Err(PipelineError::ParseError { index: 1, .. }) => {}
        other => panic!("expected ParseError at index 1, got {other:?}"),
    }
}

#[test]
fn test_pipeline_empty() {
    let result = verify_and_compose_pipeline(&[]);
    assert!(matches!(result, Err(PipelineError::EmptyPipeline)));
}

// ---------------------------------------------------------------------------
// 6. Error cases: mismatched dimensions / invalid coefficients
// ---------------------------------------------------------------------------

#[test]
fn test_compose_mismatched_variables_fails() {
    // cert_a concludes on x, cert_b premises on y -- no match.
    let cert_a = build_simple_entailment("x", 1, 3, 5);
    let cert_b = build_simple_entailment("y", 1, 5, 7);

    let err = compose_entailment_certs(&cert_a, &cert_b)
        .expect_err("mismatched variable names should fail composition");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_mismatched_bounds_fails() {
    // cert_a concludes x <= 5, cert_b premises on x <= 6 -- no structural match.
    let cert_a = build_simple_entailment("x", 1, 3, 5);
    let cert_b = build_simple_entailment("x", 1, 6, 8);

    let err = compose_entailment_certs(&cert_a, &cert_b)
        .expect_err("mismatched bounds should fail composition");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_verify_invalid_entailment_bound_direction() {
    // Claims x <= 5 implies x <= 3 -- invalid (derived bound 5 > claimed 3).
    let mut coeffs = BTreeMap::new();
    coeffs.insert("x".to_string(), ExternalRational::from_int(1));

    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs,
            constant: ExternalRational::from_int(3),
        },
    };

    let err =
        verify_entailment_certificate(&cert).expect_err("invalid bound direction should fail");
    assert!(
        err.detail.contains("does not imply"),
        "error should mention bound implication failure: {err}"
    );
}

#[test]
fn test_verify_negative_multiplier_rejected() {
    let mut coeffs = BTreeMap::new();
    coeffs.insert("x".to_string(), ExternalRational::from_int(1));

    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::from_int(-1)],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs,
            constant: ExternalRational::from_int(6),
        },
    };

    let err =
        verify_entailment_certificate(&cert).expect_err("negative multiplier should be rejected");
    assert!(
        err.detail.contains("negative"),
        "error should mention negative multiplier: {err}"
    );
}

#[test]
fn test_verify_version_mismatch_rejected() {
    let cert = ExternalEntailmentCert {
        version: "2.0".to_string(),
        premises: vec![],
        multipliers: vec![],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::new(),
            constant: ExternalRational::ZERO,
        },
    };

    let err = verify_entailment_certificate(&cert).expect_err("version 2.0 should be rejected");
    assert!(
        err.detail.contains("unsupported"),
        "error should mention unsupported version: {err}"
    );
}

#[test]
fn test_verify_length_mismatch_rejected() {
    let mut coeffs = BTreeMap::new();
    coeffs.insert("x".to_string(), ExternalRational::from_int(1));

    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: coeffs.clone(),
                constant: ExternalRational::from_int(5),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: coeffs.clone(),
                constant: ExternalRational::from_int(3),
            },
        ],
        multipliers: vec![ExternalRational::ONE], // Only 1 multiplier for 2 premises
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs,
            constant: ExternalRational::from_int(10),
        },
    };

    let err = verify_entailment_certificate(&cert).expect_err("length mismatch should be rejected");
    assert!(
        err.detail.contains("mismatch"),
        "error should mention length mismatch: {err}"
    );
}

// ---------------------------------------------------------------------------
// 7. Round-trip: serialize composed cert, re-parse, re-verify
// ---------------------------------------------------------------------------

#[test]
fn test_compose_roundtrip_serialize_deserialize_verify() {
    let cert_a = build_simple_entailment("x", 1, 3, 5);
    let cert_b = build_simple_entailment("x", 1, 5, 8);

    let composed = compose_entailment_certs(&cert_a, &cert_b).expect("should compose");

    // Serialize to JSON, then re-parse and re-verify.
    let json =
        serde_json::to_string(&composed.certificate).expect("composed cert should serialize");
    let reparsed: ExternalEntailmentCert =
        serde_json::from_str(&json).expect("serialized cert should re-parse");
    let (derived, claimed) =
        verify_entailment_certificate(&reparsed).expect("re-parsed composed cert should verify");
    assert!(derived <= claimed);
}

// ===========================================================================
// 8. Farkas bridge: single certificate verification
// ===========================================================================

#[test]
fn test_farkas_bridge_verify_valid_1d() {
    // x in [-1, 1] => x in [-2, 2] (bound weakening)
    let cert = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);
}

#[test]
fn test_farkas_bridge_verify_valid_2d() {
    // (x,y) in [-1,1]x[-2,2] => (x,y) in [-3,3]x[-4,4]
    let cert = build_simple_box_cert(2, &[-1.0, -2.0], &[1.0, 2.0], &[-3.0, -4.0], &[3.0, 4.0]);
    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);
}

#[test]
fn test_farkas_bridge_verify_identity_bounds() {
    // x in [0, 1] => x in [0, 1] (identity, bounds equal)
    let cert = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[1.0]);
    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);
}

#[test]
fn test_farkas_bridge_verify_negative_multiplier() {
    let mut cert = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    cert.multipliers[0] = -1.0;
    let result = verify_farkas_bridge(&cert);
    assert!(
        matches!(
            result,
            FarkasVerifyResult::NegativeMultiplier { index: 0, .. }
        ),
        "expected NegativeMultiplier, got {result:?}"
    );
}

#[test]
fn test_farkas_bridge_verify_dimension_error_multipliers() {
    let mut cert = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    // Remove one multiplier to create mismatch.
    cert.multipliers.pop();
    let result = verify_farkas_bridge(&cert);
    assert!(
        matches!(result, FarkasVerifyResult::DimensionError { .. }),
        "expected DimensionError, got {result:?}"
    );
}

#[test]
fn test_farkas_bridge_verify_dimension_error_input_row() {
    let mut cert = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    // Corrupt an input matrix row to have wrong dimension.
    cert.input_matrix[0] = vec![1.0, 0.0, 0.0]; // 3 elements instead of 2
    let result = verify_farkas_bridge(&cert);
    assert!(
        matches!(
            result,
            FarkasVerifyResult::DimensionError {
                expected: 2,
                got: 3
            }
        ),
        "expected DimensionError, got {result:?}"
    );
}

// ===========================================================================
// 9. Farkas bridge: farkas_to_interval conversion
// ===========================================================================

#[test]
fn test_farkas_to_interval_1d() {
    let cert = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let (input, output) = farkas_to_interval(&cert).expect("should convert");

    assert_eq!(input.len(), 1);
    assert!((input[0].lower - (-1.0)).abs() < 1e-9);
    assert!((input[0].upper - 1.0).abs() < 1e-9);

    assert_eq!(output.len(), 1);
    assert!((output[0].lower - (-2.0)).abs() < 1e-9);
    assert!((output[0].upper - 2.0).abs() < 1e-9);
}

#[test]
fn test_farkas_to_interval_2d() {
    let cert = build_simple_box_cert(2, &[-1.0, -3.0], &[2.0, 4.0], &[-5.0, -6.0], &[5.0, 6.0]);
    let (input, output) = farkas_to_interval(&cert).expect("should convert 2d");

    assert_eq!(input.len(), 2);
    assert!((input[0].lower - (-1.0)).abs() < 1e-9);
    assert!((input[0].upper - 2.0).abs() < 1e-9);
    assert!((input[1].lower - (-3.0)).abs() < 1e-9);
    assert!((input[1].upper - 4.0).abs() < 1e-9);

    assert_eq!(output.len(), 2);
    assert!((output[0].lower - (-5.0)).abs() < 1e-9);
    assert!((output[0].upper - 5.0).abs() < 1e-9);
}

#[test]
fn test_farkas_to_interval_invalid_cert_rejected() {
    let mut cert = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    cert.multipliers[0] = -5.0; // invalid
    let err = farkas_to_interval(&cert).expect_err("invalid cert should fail");
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_farkas_to_interval_non_box_rejected() {
    // Create a certificate with non-box constraints (diagonal matrix).
    let cert = ExternalFarkasCert {
        multipliers: vec![1.0, 1.0],
        input_matrix: vec![vec![1.0, 1.0], vec![-1.0, -1.0]], // x+y <= b, not box
        input_bounds: vec![2.0, 2.0],
        output_matrix: vec![
            vec![1.0, 0.0],
            vec![-1.0, 0.0],
            vec![0.0, 1.0],
            vec![0.0, -1.0],
        ],
        output_bounds: vec![3.0, 3.0, 3.0, 3.0],
        input_dim: 2,
        output_dim: 2,
    };
    let err = farkas_to_interval(&cert);
    // Should fail either on verification or on non-box detection.
    assert!(err.is_err());
}

// ===========================================================================
// 10. Box constraint round-trip: interval -> constraints -> interval
// ===========================================================================

#[test]
fn test_box_roundtrip_1d() {
    let intervals = vec![Interval::new(-3.0, 7.0)];
    let (matrix, bounds) = interval_to_box_constraints(&intervals);

    assert_eq!(matrix.len(), 2);
    assert_eq!(bounds.len(), 2);

    // Row 0: x <= 7 => [1.0], bound = 7
    assert!((matrix[0][0] - 1.0).abs() < 1e-9);
    assert!((bounds[0] - 7.0).abs() < 1e-9);
    // Row 1: -x <= 3 => [-1.0], bound = 3
    assert!((matrix[1][0] - (-1.0)).abs() < 1e-9);
    assert!((bounds[1] - 3.0).abs() < 1e-9);

    let recovered = box_constraints_to_interval(&matrix, &bounds, 1).expect("should recover");
    assert_eq!(recovered.len(), 1);
    assert!((recovered[0].lower - (-3.0)).abs() < 1e-9);
    assert!((recovered[0].upper - 7.0).abs() < 1e-9);
}

#[test]
fn test_box_roundtrip_3d() {
    let intervals = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(0.0, 5.0),
        Interval::new(-10.0, -2.0),
    ];
    let (matrix, bounds) = interval_to_box_constraints(&intervals);
    assert_eq!(matrix.len(), 6);

    let recovered = box_constraints_to_interval(&matrix, &bounds, 3).expect("should recover 3d");
    assert_eq!(recovered.len(), 3);
    for (orig, rec) in intervals.iter().zip(recovered.iter()) {
        assert!((orig.lower - rec.lower).abs() < 1e-9);
        assert!((orig.upper - rec.upper).abs() < 1e-9);
    }
}

#[test]
fn test_box_roundtrip_point_interval() {
    let intervals = vec![Interval::point(42.0)];
    let (matrix, bounds) = interval_to_box_constraints(&intervals);
    let recovered = box_constraints_to_interval(&matrix, &bounds, 1).expect("should recover point");
    assert!((recovered[0].lower - 42.0).abs() < 1e-9);
    assert!((recovered[0].upper - 42.0).abs() < 1e-9);
}

#[test]
fn test_box_constraints_to_interval_wrong_row_count() {
    // Only 3 rows for dim=2 (needs 4).
    let matrix = vec![vec![1.0, 0.0], vec![-1.0, 0.0], vec![0.0, 1.0]];
    let bounds = vec![1.0, 1.0, 1.0];
    let err = box_constraints_to_interval(&matrix, &bounds, 2).expect_err("should fail");
    assert!(matches!(err, FarkasBridgeError::NonBoxConstraints));
}

#[test]
fn test_box_constraints_to_interval_non_unit_vector() {
    // Row with coefficient 2.0 instead of 1.0.
    let matrix = vec![vec![2.0], vec![-1.0]];
    let bounds = vec![1.0, 1.0];
    let err = box_constraints_to_interval(&matrix, &bounds, 1).expect_err("should fail");
    assert!(matches!(err, FarkasBridgeError::NonBoxConstraints));
}

#[test]
fn test_box_constraints_to_interval_zero_row() {
    // Row with all zeros.
    let matrix = vec![vec![0.0], vec![0.0]];
    let bounds = vec![1.0, 1.0];
    let err = box_constraints_to_interval(&matrix, &bounds, 1).expect_err("should fail");
    assert!(matches!(err, FarkasBridgeError::NonBoxConstraints));
}

// ===========================================================================
// 11. Certificate chaining
// ===========================================================================

#[test]
fn test_chain_two_certs_1d() {
    // cert1: x in [-1, 1] => x in [-2, 2]
    // cert2: x in [-2, 2] => x in [-3, 3]
    let cert1 = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let cert2 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-3.0], &[3.0]);

    let chained = chain_farkas_certs(&cert1, &cert2).expect("should chain");

    // Chained: input from cert1, output from cert2.
    assert_eq!(chained.input_dim, 1);
    assert_eq!(chained.output_dim, 1);

    // Verify the chained certificate.
    let result = verify_farkas_bridge(&chained);
    assert_eq!(
        result,
        FarkasVerifyResult::Valid,
        "chained cert should be valid"
    );
}

#[test]
fn test_chain_two_certs_2d() {
    // cert1: (x,y) in [-1,1]x[-1,1] => (x,y) in [-2,2]x[-2,2]
    // cert2: (x,y) in [-2,2]x[-2,2] => (x,y) in [-5,5]x[-5,5]
    let cert1 = build_simple_box_cert(2, &[-1.0, -1.0], &[1.0, 1.0], &[-2.0, -2.0], &[2.0, 2.0]);
    let cert2 = build_simple_box_cert(2, &[-2.0, -2.0], &[2.0, 2.0], &[-5.0, -5.0], &[5.0, 5.0]);

    let chained = chain_farkas_certs(&cert1, &cert2).expect("should chain 2d");
    assert_eq!(chained.input_dim, 2);
    assert_eq!(chained.output_dim, 2);
}

#[test]
fn test_chain_interface_mismatch_dimension() {
    // cert1 output dim 1, cert2 input dim 2 => mismatch.
    let cert1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let cert2 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);

    let err = chain_farkas_certs(&cert1, &cert2).expect_err("should fail on dim mismatch");
    assert!(
        matches!(err, FarkasBridgeError::DimensionMismatch { .. }),
        "expected DimensionMismatch, got {err:?}"
    );
}

#[test]
fn test_chain_interface_mismatch_bounds() {
    // cert1 output: x in [-2, 2], cert2 input: x in [-3, 3] => structural mismatch.
    let cert1 = build_simple_box_cert(1, &[0.0], &[1.0], &[-2.0], &[2.0]);
    let cert2 = build_simple_box_cert(1, &[-3.0], &[3.0], &[-5.0], &[5.0]);

    let err = chain_farkas_certs(&cert1, &cert2).expect_err("should fail on bound mismatch");
    assert!(
        matches!(err, FarkasBridgeError::InterfaceMismatch),
        "expected InterfaceMismatch, got {err:?}"
    );
}

#[test]
fn test_chain_invalid_cert_rejected() {
    let mut cert1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    cert1.multipliers[0] = -1.0; // invalid
    let cert2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);

    let err = chain_farkas_certs(&cert1, &cert2).expect_err("should reject invalid cert1");
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

// ===========================================================================
// 12. Concrete examples: simple 2D linear network
// ===========================================================================

#[test]
fn test_farkas_bridge_2d_linear_network_block() {
    // Simulates a linear network block: input in [-1,1]x[-1,1], output in [-2,2]x[-2,2].
    // This models a weight matrix that at most doubles the bounds.
    let cert = build_simple_box_cert(2, &[-1.0, -1.0], &[1.0, 1.0], &[-2.0, -2.0], &[2.0, 2.0]);

    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);

    let (input_ivs, output_ivs) = farkas_to_interval(&cert).expect("should convert");
    assert_eq!(input_ivs.len(), 2);
    assert_eq!(output_ivs.len(), 2);

    // Verify interval widths.
    assert!((input_ivs[0].width() - 2.0).abs() < 1e-9);
    assert!((output_ivs[0].width() - 4.0).abs() < 1e-9);
}

#[test]
fn test_farkas_bridge_relu_positive_range_cert() {
    // ReLU in the positive range: input in [0, 1] => output in [0, 1] (identity).
    // This is a valid bound-weakening cert (output bounds equal input bounds).
    let cert = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[1.0]);
    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);

    let (input_ivs, output_ivs) = farkas_to_interval(&cert).expect("should convert relu block");
    assert!((input_ivs[0].lower - 0.0).abs() < 1e-9);
    assert!((output_ivs[0].lower - 0.0).abs() < 1e-9);
    assert!((output_ivs[0].upper - 1.0).abs() < 1e-9);
}

#[test]
fn test_farkas_bridge_relu_tightening_rejected() {
    // ReLU with tightened lower bound: input [-1, 1] => output [0, 1].
    // This is NOT a valid bound-weakening cert (output lower is tighter).
    // The identity multiplier cert should fail verification.
    let cert = build_simple_box_cert(1, &[-1.0], &[1.0], &[0.0], &[1.0]);
    let result = verify_farkas_bridge(&cert);
    assert!(
        matches!(result, FarkasVerifyResult::ConstraintMismatch { .. }),
        "cert that tightens bounds should fail: {result:?}"
    );
}

// ===========================================================================
// 13. Pipeline end-to-end with Farkas bridge: create, verify, compose, extract
// ===========================================================================

#[test]
fn test_farkas_bridge_full_pipeline_3_blocks() {
    // Block 1: [-2, 2] => [-3, 3]
    // Block 2: [-3, 3] => [-5, 5]
    // Block 3: [-5, 5] => [-10, 10]
    let b1 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-3.0], &[3.0]);
    let b2 = build_simple_box_cert(1, &[-3.0], &[3.0], &[-5.0], &[5.0]);
    let b3 = build_simple_box_cert(1, &[-5.0], &[5.0], &[-10.0], &[10.0]);

    // Step 1: Verify each certificate.
    assert_eq!(verify_farkas_bridge(&b1), FarkasVerifyResult::Valid);
    assert_eq!(verify_farkas_bridge(&b2), FarkasVerifyResult::Valid);
    assert_eq!(verify_farkas_bridge(&b3), FarkasVerifyResult::Valid);

    // Step 2: Chain b1 -> b2.
    let chained_12 = chain_farkas_certs(&b1, &b2).expect("b1->b2 should chain");

    // Step 3: Chain (b1->b2) -> b3.
    let chained_123 = chain_farkas_certs(&chained_12, &b3).expect("b12->b3 should chain");

    // Step 4: Extract intervals from the fully chained certificate.
    let (input_ivs, output_ivs) =
        farkas_to_interval(&chained_123).expect("should extract intervals");

    // Input should be block 1 input: [-2, 2]
    assert_eq!(input_ivs.len(), 1);
    assert!((input_ivs[0].lower - (-2.0)).abs() < 1e-9);
    assert!((input_ivs[0].upper - 2.0).abs() < 1e-9);

    // Output should be block 3 output: [-10, 10]
    assert_eq!(output_ivs.len(), 1);
    assert!((output_ivs[0].lower - (-10.0)).abs() < 1e-9);
    assert!((output_ivs[0].upper - 10.0).abs() < 1e-9);
}

#[test]
fn test_interval_to_box_constraints_empty() {
    let (matrix, bounds) = interval_to_box_constraints(&[]);
    assert!(matrix.is_empty());
    assert!(bounds.is_empty());
}

#[test]
fn test_box_constraints_to_interval_bounds_length_mismatch() {
    let matrix = vec![vec![1.0], vec![-1.0]];
    let bounds = vec![1.0]; // Only 1 bound for 2 rows.
    let err = box_constraints_to_interval(&matrix, &bounds, 1).expect_err("should fail");
    assert!(matches!(err, FarkasBridgeError::DimensionMismatch { .. }));
}

#[test]
fn test_farkas_bridge_verify_3d_valid() {
    let cert = build_simple_box_cert(
        3,
        &[-1.0, -2.0, -3.0],
        &[1.0, 2.0, 3.0],
        &[-4.0, -5.0, -6.0],
        &[4.0, 5.0, 6.0],
    );
    let result = verify_farkas_bridge(&cert);
    assert_eq!(result, FarkasVerifyResult::Valid);
}

#[test]
fn test_farkas_to_interval_3d_roundtrip() {
    let cert = build_simple_box_cert(
        3,
        &[0.0, 1.0, 2.0],
        &[3.0, 4.0, 5.0],
        &[-1.0, 0.0, 1.0],
        &[4.0, 5.0, 6.0],
    );
    let (input_ivs, output_ivs) = farkas_to_interval(&cert).expect("should convert 3d");

    assert_eq!(input_ivs.len(), 3);
    assert_eq!(output_ivs.len(), 3);

    assert!((input_ivs[0].lower - 0.0).abs() < 1e-9);
    assert!((input_ivs[0].upper - 3.0).abs() < 1e-9);
    assert!((input_ivs[2].lower - 2.0).abs() < 1e-9);
    assert!((input_ivs[2].upper - 5.0).abs() < 1e-9);

    assert!((output_ivs[0].lower - (-1.0)).abs() < 1e-9);
    assert!((output_ivs[2].upper - 6.0).abs() < 1e-9);
}
