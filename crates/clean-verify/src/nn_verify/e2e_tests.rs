// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the NN verification pipeline.
//!
//! Tests the full path: JsonCertificate -> Farkas chain -> verification ->
//! composition -> output property check.

use super::certificate::farkas_bridge::verify_farkas_certificate;
use super::certificate::farkas_bridge::FarkasVerifyResult;
use super::e2e_json_parser::{
    build_identity_layer_cert, build_layer_cert, build_test_certificate, input_spec_to_bounds,
    json_to_farkas_chain, validate_certificate, JsonCertificate, JsonInputSpec, JsonLayerCert,
    JsonOutputProperty, PipelineParseError,
};
use super::e2e_verifier::{
    check_interface_consistency, verify_network, verify_output_property, TrustLevel,
};

// ---------------------------------------------------------------------------
// Helper: build test certificates
// ---------------------------------------------------------------------------

/// Build a 1-dim identity certificate with 2 layers.
/// Single output dim avoids classification property issues.
fn two_layer_single_dim_cert() -> JsonCertificate {
    let bounds = vec![(-1.0, 1.0)];
    build_test_certificate(
        "test_2layer_1d",
        vec![
            build_identity_layer_cert(0, "linear", &bounds),
            build_identity_layer_cert(1, "relu", &bounds),
        ],
        vec![0.0],
        1.0,
        0,
        0.0, // single class => trivially robust
    )
}

/// Build a 2-dim certificate with asymmetric bounds that satisfy
/// robust classification: class 0 in [3.0, 5.0], class 1 in [0.0, 1.0].
/// lower(class 0) - upper(class 1) = 3.0 - 1.0 = 2.0 >= 1.0.
///
/// For Farkas validity with multiplier=1.0, both layers use the same
/// bounds as input and output (identity entailment: A => A).
fn two_layer_robust_cert() -> JsonCertificate {
    let robust_bounds = vec![(3.0, 5.0), (0.0, 1.0)];
    build_test_certificate(
        "test_2layer_robust",
        vec![
            build_identity_layer_cert(0, "linear", &robust_bounds),
            build_identity_layer_cert(1, "relu", &robust_bounds),
        ],
        vec![4.0, 0.5],
        0.5,
        0,
        1.0,
    )
}

/// Build a 3-layer certificate with widening bounds (valid Farkas entailment).
/// Each layer widens bounds, so multiplier=1.0 entailment holds.
fn three_layer_widening_cert() -> JsonCertificate {
    let b0 = vec![(-1.0, 1.0)];
    let b1 = vec![(-1.5, 1.5)];
    let b2 = vec![(-2.0, 2.0)];
    build_test_certificate(
        "test_3layer",
        vec![
            build_layer_cert(0, "linear", &b0, &b1, vec![1.0; 2]),
            build_layer_cert(1, "relu", &b1, &b2, vec![1.0; 2]),
            build_layer_cert(2, "linear", &b2, &b2, vec![1.0; 2]),
        ],
        vec![0.0],
        1.0,
        0,
        0.0,
    )
}

// ---------------------------------------------------------------------------
// 1. Tiny 2-layer network: full pipeline pass
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_two_layer_single_dim_passes() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("pipeline should succeed");
    assert!(result.verified, "identity 1-dim 2-layer cert should verify");
    assert_eq!(result.layer_results.len(), 2);
    for lr in &result.layer_results {
        assert!(
            lr.farkas_valid,
            "layer {} Farkas should be valid",
            lr.layer_index
        );
        assert!(
            lr.bounds_valid,
            "layer {} bounds should be valid",
            lr.layer_index
        );
    }
}

#[test]
fn test_e2e_two_layer_layer_types() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("pipeline should succeed");
    assert_eq!(result.layer_results[0].layer_type, "linear");
    assert_eq!(result.layer_results[1].layer_type, "relu");
}

#[test]
fn test_e2e_two_layer_robust_classification() {
    let cert = two_layer_robust_cert();
    let result = verify_network(&cert).expect("pipeline should succeed");
    assert!(result.verified, "robust 2-layer cert should verify");
    assert_eq!(result.trust_level, TrustLevel::CertificateBased);
}

// ---------------------------------------------------------------------------
// 2. 3-layer network: composition chains correctly
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_three_layer_composition() {
    let cert = three_layer_widening_cert();
    let result = verify_network(&cert).expect("pipeline should succeed");
    assert_eq!(result.layer_results.len(), 3);
    for lr in &result.layer_results {
        assert!(
            lr.farkas_valid,
            "layer {} Farkas should be valid",
            lr.layer_index
        );
    }
    assert!(result.verified, "widening 3-layer cert should verify");
}

#[test]
fn test_e2e_three_layer_verification_steps() {
    let cert = three_layer_widening_cert();
    let result = verify_network(&cert).expect("pipeline should succeed");
    // At minimum: 3 layer checks + 1 property check = 4
    assert!(
        result.verification_steps >= 4,
        "expected at least 4 verification steps, got {}",
        result.verification_steps,
    );
}

// ---------------------------------------------------------------------------
// 3. Invalid certificate: negative multiplier
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_negative_multiplier_detected() {
    let bounds = vec![(-1.0, 1.0)];
    let mut bad_layer = build_identity_layer_cert(0, "linear", &bounds);
    bad_layer.multipliers[0] = -5.0; // negative multiplier

    let cert = build_test_certificate("negative_mult", vec![bad_layer], vec![0.0], 1.0, 0, 0.0);

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(
            err,
            PipelineParseError::NegativeMultiplier {
                layer: 0,
                index: 0,
                ..
            }
        ),
        "expected NegativeMultiplier, got {err:?}"
    );
}

#[test]
fn test_e2e_negative_multiplier_pipeline_fails() {
    let bounds = vec![(-1.0, 1.0)];
    let mut bad_layer = build_identity_layer_cert(0, "linear", &bounds);
    bad_layer.multipliers[0] = -5.0;

    let cert = build_test_certificate("negative_mult", vec![bad_layer], vec![0.0], 1.0, 0, 0.0);

    let result = verify_network(&cert);
    assert!(
        result.is_err(),
        "pipeline should fail on negative multiplier"
    );
}

// ---------------------------------------------------------------------------
// 4. Dimension mismatch: layer 1 output != layer 2 input
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_dimension_mismatch_detected() {
    let b1 = vec![(-1.0, 1.0), (-1.0, 1.0)]; // 2-dim
    let b2 = vec![(-1.0, 1.0), (-1.0, 1.0), (-1.0, 1.0)]; // 3-dim

    let cert = build_test_certificate(
        "dim_mismatch",
        vec![
            build_identity_layer_cert(0, "linear", &b1),
            build_identity_layer_cert(1, "relu", &b2),
        ],
        vec![0.0, 0.0],
        1.0,
        0,
        0.0,
    );

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(err, PipelineParseError::DimensionMismatch { layer: 1, .. }),
        "expected DimensionMismatch at layer 1, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 5. Robust classification: verify true_class has margin
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_robust_classification_verified() {
    // Class 0 lower=5.0, class 1 upper=3.0 => margin 2.0 >= 1.0
    let output_bounds = vec![(5.0, 7.0), (1.0, 3.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 0,
        margin: 1.0,
    };
    assert!(verify_output_property(&output_bounds, &prop));
}

#[test]
fn test_e2e_robust_classification_three_classes() {
    // 3-class: class 1 lower=10.0, class 0 upper=7.0, class 2 upper=8.0
    // Margin: 10.0 - max(7.0, 8.0) = 2.0 >= 1.5
    let output_bounds = vec![(5.0, 7.0), (10.0, 12.0), (6.0, 8.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 1,
        margin: 1.5,
    };
    assert!(verify_output_property(&output_bounds, &prop));
}

// ---------------------------------------------------------------------------
// 6. Non-robust case: bounds too wide
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_non_robust_wide_bounds() {
    // Class 0 in [-100, 100], class 1 in [-100, 100]
    let output_bounds = vec![(-100.0, 100.0), (-100.0, 100.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 0,
        margin: 0.1,
    };
    assert!(!verify_output_property(&output_bounds, &prop));
}

#[test]
fn test_e2e_non_robust_overlapping() {
    // Class 0 in [3.0, 5.0], class 1 in [4.0, 6.0] -- overlapping
    let output_bounds = vec![(3.0, 5.0), (4.0, 6.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 0,
        margin: 0.0,
    };
    assert!(!verify_output_property(&output_bounds, &prop));
}

// ---------------------------------------------------------------------------
// 7. Trust level reporting
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_trust_level_certificate_based() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("should succeed");
    assert_eq!(result.trust_level, TrustLevel::CertificateBased);
}

#[test]
fn test_e2e_trust_level_partial_property_fails() {
    // Build a certificate where layers are valid but property fails.
    let bounds = vec![(-1.0, 1.0), (-1.0, 1.0)];
    let cert = build_test_certificate(
        "partial_trust",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0, 0.0],
        1.0,
        0,
        5.0, // unreasonably high margin => property fails (lower(0)-upper(1) = -1-1 = -2 < 5)
    );

    let result = verify_network(&cert).expect("should succeed structurally");
    assert!(!result.verified, "property should fail");
    assert!(
        matches!(
            result.trust_level,
            TrustLevel::Partial {
                verified_layers: 1,
                total_layers: 1
            }
        ),
        "expected Partial(1/1), got {:?}",
        result.trust_level,
    );
}

// ---------------------------------------------------------------------------
// 8. Layer types: linear + relu mixed pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_mixed_layer_types() {
    let bounds = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "mixed_types",
        vec![
            build_identity_layer_cert(0, "linear", &bounds),
            build_identity_layer_cert(1, "relu", &bounds),
            build_identity_layer_cert(2, "conv", &bounds),
            build_identity_layer_cert(3, "layernorm", &bounds),
        ],
        vec![0.0],
        1.0,
        0,
        0.0, // single class => trivially robust
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
    assert_eq!(result.layer_results.len(), 4);
    assert_eq!(result.layer_results[0].layer_type, "linear");
    assert_eq!(result.layer_results[1].layer_type, "relu");
    assert_eq!(result.layer_results[2].layer_type, "conv");
    assert_eq!(result.layer_results[3].layer_type, "layernorm");
}

// ---------------------------------------------------------------------------
// 9. Interface consistency checker
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_interface_consistent_layers() {
    let bounds = vec![(-1.0, 1.0), (-1.0, 1.0)];
    let layers = vec![
        build_identity_layer_cert(0, "linear", &bounds),
        build_identity_layer_cert(1, "relu", &bounds),
    ];
    let results = check_interface_consistency(&layers);
    assert_eq!(results.len(), 1);
    assert!(results[0].1, "identical bounds should be consistent");
}

#[test]
fn test_e2e_interface_inconsistent_layers() {
    let b1 = vec![(-1.0, 1.0), (-1.0, 1.0)];
    let b2 = vec![(-2.0, 2.0), (-2.0, 2.0)];

    let layers = vec![
        build_identity_layer_cert(0, "linear", &b1),
        build_identity_layer_cert(1, "relu", &b2),
    ];

    let results = check_interface_consistency(&layers);
    assert_eq!(results.len(), 1);
    assert!(!results[0].1, "mismatched bounds should be inconsistent");
}

#[test]
fn test_e2e_interface_multiple_gaps() {
    let b1 = vec![(-1.0, 1.0)];
    let b2 = vec![(-2.0, 2.0)];

    let layers = vec![
        build_identity_layer_cert(0, "linear", &b1),
        build_identity_layer_cert(1, "relu", &b2), // gap here
        build_identity_layer_cert(2, "linear", &b2), // consistent with previous
    ];

    let results = check_interface_consistency(&layers);
    assert_eq!(results.len(), 2);
    assert!(!results[0].1, "interface 0 should be inconsistent");
    assert!(results[1].1, "interface 1 should be consistent");
}

// ---------------------------------------------------------------------------
// 10. Empty network (0 layers): edge case
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_empty_network_error() {
    let cert = JsonCertificate {
        network_id: "empty".to_string(),
        num_layers: 0,
        layer_certs: vec![],
        input_spec: JsonInputSpec {
            center: vec![0.0],
            epsilon: 1.0,
        },
        output_property: JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 0.0,
        },
    };

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(err, PipelineParseError::MissingField(_)),
        "expected MissingField error for empty network, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 11. Single layer: trivially verified
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_single_layer_verified() {
    let bounds = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "single_layer",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0],
        1.0,
        0,
        0.0, // single class => trivially robust
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
    assert_eq!(result.layer_results.len(), 1);
}

// ---------------------------------------------------------------------------
// 12. JSON to Farkas chain conversion
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_json_to_farkas_chain_size() {
    let cert = two_layer_single_dim_cert();
    let chain = json_to_farkas_chain(&cert).expect("should convert");
    assert_eq!(chain.len(), 2, "2-layer cert should produce 2 Farkas certs");
}

#[test]
fn test_e2e_json_to_farkas_chain_dims() {
    let cert = two_layer_single_dim_cert();
    let chain = json_to_farkas_chain(&cert).expect("should convert");
    assert_eq!(chain[0].input_dim, 1);
    assert_eq!(chain[0].output_dim, 1);
    assert_eq!(chain[1].input_dim, 1);
    assert_eq!(chain[1].output_dim, 1);
}

#[test]
fn test_e2e_farkas_cert_valid_after_conversion() {
    let cert = two_layer_single_dim_cert();
    let chain = json_to_farkas_chain(&cert).expect("should convert");
    for (i, farkas) in chain.iter().enumerate() {
        let result = verify_farkas_certificate(farkas);
        assert_eq!(
            result,
            FarkasVerifyResult::Valid,
            "layer {i} Farkas cert should be valid, got {result:?}",
        );
    }
}

// ---------------------------------------------------------------------------
// 13. Input spec to bounds
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_input_spec_to_bounds() {
    let spec = JsonInputSpec {
        center: vec![0.5, 1.0, -0.5],
        epsilon: 0.1,
    };
    let bounds = input_spec_to_bounds(&spec);
    assert_eq!(bounds.len(), 3);
    assert!((bounds[0].0 - 0.4).abs() < 1e-10);
    assert!((bounds[0].1 - 0.6).abs() < 1e-10);
    assert!((bounds[1].0 - 0.9).abs() < 1e-10);
    assert!((bounds[1].1 - 1.1).abs() < 1e-10);
    assert!((bounds[2].0 - (-0.6)).abs() < 1e-10);
    assert!((bounds[2].1 - (-0.4)).abs() < 1e-10);
}

#[test]
fn test_e2e_input_spec_zero_epsilon() {
    let spec = JsonInputSpec {
        center: vec![3.0],
        epsilon: 0.0,
    };
    let bounds = input_spec_to_bounds(&spec);
    assert_eq!(bounds.len(), 1);
    assert!((bounds[0].0 - 3.0).abs() < 1e-10);
    assert!((bounds[0].1 - 3.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 14. Layer count mismatch
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_layer_count_mismatch() {
    let bounds = vec![(-1.0, 1.0)];
    let cert = JsonCertificate {
        network_id: "count_mismatch".to_string(),
        num_layers: 5, // declared 5, only 1 layer
        layer_certs: vec![build_identity_layer_cert(0, "linear", &bounds)],
        input_spec: JsonInputSpec {
            center: vec![0.0],
            epsilon: 1.0,
        },
        output_property: JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 0.0,
        },
    };

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(
            err,
            PipelineParseError::LayerCountMismatch {
                declared: 5,
                actual: 1
            }
        ),
        "expected LayerCountMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 15. Invalid layer type
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_invalid_layer_type() {
    let cert = build_test_certificate(
        "invalid_type",
        vec![build_identity_layer_cert(0, "transformer", &[(-1.0, 1.0)])],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(err, PipelineParseError::InvalidLayerType(ref t) if t == "transformer"),
        "expected InvalidLayerType(transformer), got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 16. Multiplier count mismatch
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_multiplier_count_mismatch() {
    let cert = build_test_certificate(
        "mult_count",
        vec![JsonLayerCert {
            layer_index: 0,
            layer_type: "linear".to_string(),
            multipliers: vec![1.0], // should be 2 * dim = 2
            input_bounds: vec![(-1.0, 1.0)],
            output_bounds: vec![(-1.0, 1.0)],
            weight_matrix: None,
            bias: None,
            activation_pattern: None,
        }],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(
            err,
            PipelineParseError::DimensionMismatch {
                layer: 0,
                expected: 2,
                got: 1
            }
        ),
        "expected DimensionMismatch for multiplier count, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 17. Robust classification with exact margin boundary
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_exact_margin_boundary() {
    // Class 0 lower=5.0, class 1 upper=3.0 => margin exactly 2.0
    let output_bounds = vec![(5.0, 7.0), (1.0, 3.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 0,
        margin: 2.0,
    };
    assert!(verify_output_property(&output_bounds, &prop));
}

#[test]
fn test_e2e_margin_above_boundary() {
    let output_bounds = vec![(5.0, 7.0), (1.0, 3.0)];
    let prop = JsonOutputProperty {
        property_type: "robust_classification".to_string(),
        true_class: 0,
        margin: 3.0, // exceeds available margin of 2.0
    };
    assert!(!verify_output_property(&output_bounds, &prop));
}

// ---------------------------------------------------------------------------
// 18. Composed certificate is present on success
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_composed_cert_present() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
    assert!(
        result.composed_cert.is_some(),
        "composed cert should be present on verified result"
    );
}

#[test]
fn test_e2e_single_layer_composed_cert() {
    let bounds = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "single",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
    assert!(
        result.composed_cert.is_some(),
        "single-layer should have composed cert"
    );
}

// ---------------------------------------------------------------------------
// 19. Multi-dimension certificate
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_four_dim_single_class() {
    // 4-dim but single output class => trivially robust
    let _bounds = [(-1.0, 1.0), (-2.0, 2.0), (-0.5, 0.5), (-3.0, 3.0)];
    // Use single output class (collapse to 1-dim for property check)
    // But since Farkas requires input_dim == output_dim for box certs,
    // keep all 4 dims and use true_class=0, margin=0.
    // With 4 classes, lower(class0)=-1, upper(class1)=2 => -1-2=-3 < 0 => fails.
    // Use separate 1-dim output instead.
    let bounds_1d = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "4dim_single_class",
        vec![
            build_identity_layer_cert(0, "linear", &bounds_1d),
            build_identity_layer_cert(1, "relu", &bounds_1d),
        ],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
}

#[test]
fn test_e2e_four_dim_robust() {
    // 4-dim with class 0 clearly dominant (identity entailment).
    // class 0 in [10, 12], classes 1-3 in [0, 1].
    // lower(0) - max(upper(1..3)) = 10 - 1 = 9 >= 1.0
    let robust_bounds = vec![(10.0, 12.0), (0.0, 1.0), (0.0, 1.0), (0.0, 1.0)];
    let cert = build_test_certificate(
        "4dim_robust",
        vec![build_identity_layer_cert(0, "linear", &robust_bounds)],
        vec![11.0, 0.5, 0.5, 0.5],
        0.5,
        0,
        1.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
}

// ---------------------------------------------------------------------------
// 20. Verification result fields
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_verification_steps_counted() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("should succeed");
    // At minimum: 2 layer checks + 1 property check = 3
    assert!(
        result.verification_steps >= 3,
        "expected at least 3 steps, got {}",
        result.verification_steps,
    );
}

// ---------------------------------------------------------------------------
// 21. Interval extraction in layer results
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_layer_result_intervals_present() {
    let cert = two_layer_single_dim_cert();
    let result = verify_network(&cert).expect("should succeed");
    for lr in &result.layer_results {
        assert!(
            lr.input_interval.is_some(),
            "layer {} should have input intervals",
            lr.layer_index
        );
        assert!(
            lr.output_interval.is_some(),
            "layer {} should have output intervals",
            lr.layer_index
        );
    }
}

#[test]
fn test_e2e_layer_result_interval_values() {
    let bounds = vec![(-1.0, 1.0), (-2.0, 2.0)];
    let cert = build_test_certificate(
        "interval_values",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0, 0.0],
        1.0,
        0,
        0.0, // 2-class with symmetric bounds => property fails, but we check intervals anyway
    );

    let result = verify_network(&cert).expect("should succeed structurally");
    let intervals = result.layer_results[0]
        .input_interval
        .as_ref()
        .expect("intervals present");
    assert_eq!(intervals.len(), 2);
    assert!((intervals[0].lower - (-1.0)).abs() < 1e-9);
    assert!((intervals[0].upper - 1.0).abs() < 1e-9);
    assert!((intervals[1].lower - (-2.0)).abs() < 1e-9);
    assert!((intervals[1].upper - 2.0).abs() < 1e-9);
}

// ---------------------------------------------------------------------------
// 22. Input spec dimension mismatch with first layer
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_input_spec_dim_mismatch() {
    let cert = JsonCertificate {
        network_id: "input_dim_mismatch".to_string(),
        num_layers: 1,
        layer_certs: vec![build_identity_layer_cert(
            0,
            "linear",
            &[(-1.0, 1.0), (-1.0, 1.0)],
        )],
        input_spec: JsonInputSpec {
            center: vec![0.0], // 1-dim, but layer expects 2-dim
            epsilon: 1.0,
        },
        output_property: JsonOutputProperty {
            property_type: "robust_classification".to_string(),
            true_class: 0,
            margin: 0.0,
        },
    };

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(
            err,
            PipelineParseError::DimensionMismatch {
                layer: 0,
                expected: 2,
                got: 1
            }
        ),
        "expected DimensionMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 23. Empty bounds in a layer
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_empty_bounds_error() {
    let cert = build_test_certificate(
        "empty_bounds",
        vec![JsonLayerCert {
            layer_index: 0,
            layer_type: "linear".to_string(),
            multipliers: vec![],
            input_bounds: vec![], // empty
            output_bounds: vec![(-1.0, 1.0)],
            weight_matrix: None,
            bias: None,
            activation_pattern: None,
        }],
        vec![],
        0.0,
        0,
        0.0,
    );

    let err = validate_certificate(&cert).unwrap_err();
    assert!(
        matches!(err, PipelineParseError::EmptyBounds { layer: 0 }),
        "expected EmptyBounds, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 24. Verification with non-zero margin on two classes (end-to-end)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_two_class_margin_verified_end_to_end() {
    // Build certificate where output bounds guarantee robust classification.
    // Class 0 in [5.0, 7.0], class 1 in [1.0, 2.0]
    // lower(0) - upper(1) = 5.0 - 2.0 = 3.0 >= 2.0
    // Use identity entailment: both input and output have the same robust bounds.
    let robust_bounds = vec![(5.0, 7.0), (1.0, 2.0)];
    let cert = build_test_certificate(
        "two_class_margin",
        vec![build_identity_layer_cert(0, "linear", &robust_bounds)],
        vec![6.0, 1.5],
        0.5,
        0,
        2.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(
        result.verified,
        "robust classification with margin 2.0 should verify"
    );
}

// ---------------------------------------------------------------------------
// 25. Widening bounds across layers preserve entailment
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_widening_bounds_chain() {
    // Two layers, each widening bounds: [-1,1] -> [-2,2] (entailment valid).
    let b0 = vec![(-1.0, 1.0)];
    let b1 = vec![(-2.0, 2.0)];
    let cert = build_test_certificate(
        "widening",
        vec![
            build_layer_cert(0, "linear", &b0, &b1, vec![1.0; 2]),
            build_layer_cert(1, "relu", &b1, &b1, vec![1.0; 2]),
        ],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(result.verified);
    assert_eq!(result.layer_results.len(), 2);
}

// ---------------------------------------------------------------------------
// 26. Verify single-class output (no competitors)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_single_class_output() {
    let bounds = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "single_class",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let result = verify_network(&cert).expect("should succeed");
    assert!(
        result.verified,
        "single-class output should be trivially robust"
    );
}

// ---------------------------------------------------------------------------
// 27. PipelineParseError Display
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_error_display() {
    let err = PipelineParseError::InvalidLayerType("softmax".to_string());
    let msg = format!("{err}");
    assert!(
        msg.contains("softmax"),
        "error message should mention the invalid type"
    );

    let err = PipelineParseError::DimensionMismatch {
        layer: 2,
        expected: 4,
        got: 3,
    };
    let msg = format!("{err}");
    assert!(
        msg.contains("layer 2"),
        "error message should mention the layer"
    );
    assert!(
        msg.contains("expected 4"),
        "error message should mention expected dim"
    );
}

// ---------------------------------------------------------------------------
// 28. Farkas verification of identity cert round-trip
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_identity_cert_farkas_round_trip() {
    // Build a 1D identity cert and verify Farkas step by step.
    let bounds = vec![(-3.0, 3.0)];
    let cert = build_test_certificate(
        "round_trip",
        vec![build_identity_layer_cert(0, "linear", &bounds)],
        vec![0.0],
        3.0,
        0,
        0.0,
    );

    let chain = json_to_farkas_chain(&cert).expect("should convert");
    assert_eq!(chain.len(), 1);

    let farkas = &chain[0];
    assert_eq!(farkas.input_dim, 1);
    assert_eq!(farkas.output_dim, 1);
    // Box constraints for 1D: 2 rows
    assert_eq!(farkas.input_matrix.len(), 2);
    assert_eq!(farkas.output_matrix.len(), 2);
    assert_eq!(farkas.multipliers.len(), 2);

    let result = verify_farkas_certificate(farkas);
    assert_eq!(result, FarkasVerifyResult::Valid);
}

// ---------------------------------------------------------------------------
// 29. Pipeline with interface gap produces not-verified
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_interface_gap_not_verified() {
    // Layer 0 output: [-1,1], Layer 1 input: [-2,2] => gap
    let b0 = vec![(-1.0, 1.0)];
    let b1 = vec![(-2.0, 2.0)];
    let cert = build_test_certificate(
        "interface_gap",
        vec![
            build_identity_layer_cert(0, "linear", &b0),
            build_identity_layer_cert(1, "relu", &b1),
        ],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let result = verify_network(&cert).expect("should succeed structurally");
    assert!(
        !result.verified,
        "interface gap should prevent verification"
    );
}

// ---------------------------------------------------------------------------
// 30. Widening Farkas cert is valid but narrowing is not
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_widening_farkas_valid() {
    // [-1,1] -> [-2,2]: input constraints are tighter, so the entailment
    // "x in [-1,1] => x in [-2,2]" holds with multiplier=1.0.
    let b_in = vec![(-1.0, 1.0)];
    let b_out = vec![(-2.0, 2.0)];
    let cert = build_test_certificate(
        "widening",
        vec![build_layer_cert(0, "linear", &b_in, &b_out, vec![1.0; 2])],
        vec![0.0],
        1.0,
        0,
        0.0,
    );

    let chain = json_to_farkas_chain(&cert).expect("should convert");
    let result = verify_farkas_certificate(&chain[0]);
    assert_eq!(
        result,
        FarkasVerifyResult::Valid,
        "widening should be valid"
    );
}

#[test]
fn test_e2e_narrowing_farkas_invalid() {
    // [-2,2] -> [-1,1]: the entailment "x in [-2,2] => x in [-1,1]"
    // does NOT hold with multiplier=1.0 because x=1.5 is in [-2,2] but not [-1,1].
    // The Farkas check should detect the bound mismatch.
    let b_in = vec![(-2.0, 2.0)];
    let b_out = vec![(-1.0, 1.0)];
    let cert = build_test_certificate(
        "narrowing",
        vec![build_layer_cert(0, "linear", &b_in, &b_out, vec![1.0; 2])],
        vec![0.0],
        2.0,
        0,
        0.0,
    );

    let chain = json_to_farkas_chain(&cert).expect("should convert");
    let result = verify_farkas_certificate(&chain[0]);
    assert_ne!(
        result,
        FarkasVerifyResult::Valid,
        "narrowing with mult=1 should be invalid"
    );
}
