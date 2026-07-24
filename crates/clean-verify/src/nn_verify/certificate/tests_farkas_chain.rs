// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Farkas certificate chaining module (`farkas_chain.rs`).

use super::farkas_bridge::{
    build_simple_box_cert, verify_farkas_certificate, ExternalFarkasCert, FarkasBridgeError,
    FarkasVerifyResult,
};
use super::farkas_chain::chain_farkas_certs;

// --- Happy path chaining ---

#[test]
fn test_chain_simple_1d_box_certs() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, 1);
    assert_eq!(chained.output_dim, 1);
}

#[test]
fn test_chain_1d_preserves_input_bounds() {
    let c1 = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-3.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_bounds, c1.input_bounds);
    assert_eq!(chained.input_matrix, c1.input_matrix);
}

#[test]
fn test_chain_1d_preserves_output_bounds() {
    let c1 = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-3.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.output_bounds, c2.output_bounds);
    assert_eq!(chained.output_matrix, c2.output_matrix);
}

#[test]
fn test_chain_2d_box_certs() {
    let c1 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, 2);
    assert_eq!(chained.output_dim, 2);
    assert_eq!(chained.input_matrix, c1.input_matrix);
    assert_eq!(chained.output_matrix, c2.output_matrix);
}

#[test]
fn test_chain_result_passes_verification_1d() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_result_passes_verification_2d() {
    let c1 = build_simple_box_cert(2, &[0.0, -1.0], &[1.0, 1.0], &[0.0, -2.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, -2.0], &[2.0, 2.0], &[0.0, -3.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_identity_multipliers_nonnegative() {
    let c1 = build_simple_box_cert(1, &[0.0], &[5.0], &[0.0], &[10.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[10.0], &[0.0], &[20.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    for &m in &chained.multipliers {
        assert!(
            m >= 0.0,
            "composed multipliers should be non-negative, got {m}"
        );
    }
}

#[test]
fn test_chain_symmetric_bounds() {
    let c1 = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-4.0], &[4.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_bounds, c1.input_bounds);
    assert_eq!(chained.output_bounds, c2.output_bounds);
}

#[test]
fn test_chain_preserves_3d_dims() {
    let c1 = build_simple_box_cert(3, &[0.0; 3], &[1.0; 3], &[0.0; 3], &[2.0; 3]);
    let c2 = build_simple_box_cert(3, &[0.0; 3], &[2.0; 3], &[0.0; 3], &[4.0; 3]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, 3);
    assert_eq!(chained.output_dim, 3);
}

#[test]
fn test_chain_asymmetric_bounds() {
    let c1 = build_simple_box_cert(1, &[1.0], &[3.0], &[0.0], &[4.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[4.0], &[-1.0], &[5.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

// --- Error paths ---

#[test]
fn test_chain_cert1_invalid_negative_multiplier() {
    let mut c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    c1.multipliers[0] = -1.0;
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_chain_cert2_invalid_negative_multiplier() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.multipliers[0] = -1.0;
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_chain_cert1_invalid_error_mentions_cert1() {
    let mut c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    c1.multipliers[0] = -5.0;
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    match chain_farkas_certs(&c1, &c2).unwrap_err() {
        FarkasBridgeError::InvalidCertificate(msg) => {
            assert!(msg.contains("cert1"), "error should mention cert1: {msg}");
        }
        other => panic!("expected InvalidCertificate, got {other:?}"),
    }
}

#[test]
fn test_chain_cert2_invalid_error_mentions_cert2() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.multipliers[1] = -5.0;
    match chain_farkas_certs(&c1, &c2).unwrap_err() {
        FarkasBridgeError::InvalidCertificate(msg) => {
            assert!(msg.contains("cert2"), "error should mention cert2: {msg}");
        }
        other => panic!("expected InvalidCertificate, got {other:?}"),
    }
}

#[test]
fn test_chain_dimension_mismatch_output_input() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(
        err,
        FarkasBridgeError::DimensionMismatch {
            expected: 1,
            got: 2
        }
    ));
}

#[test]
fn test_chain_matrix_row_count_mismatch() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.input_matrix.push(vec![1.0]);
    c2.input_bounds.push(5.0);
    c2.multipliers.push(1.0);
    // cert2 fails verification first (dimension mismatch in row count)
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(
        err,
        FarkasBridgeError::InvalidCertificate(_) | FarkasBridgeError::InterfaceMismatch
    ));
}

#[test]
fn test_chain_bounds_length_mismatch() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.input_bounds.truncate(1);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_chain_interface_mismatch_matrix_values() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.input_matrix[0][0] = 0.5; // breaks box structure
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(
        err,
        FarkasBridgeError::InvalidCertificate(_) | FarkasBridgeError::InterfaceMismatch
    ));
}

#[test]
fn test_chain_interface_mismatch_upper_bounds_differ() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[5.0], &[0.0], &[6.0]);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InterfaceMismatch));
}

#[test]
fn test_chain_interface_mismatch_lower_bounds_differ() {
    let c1 = build_simple_box_cert(1, &[0.0], &[2.0], &[-1.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[-3.0], &[2.0], &[-4.0], &[3.0]);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InterfaceMismatch));
}

// --- Multiplier composition ---

#[test]
fn test_compose_identity_multipliers_1d() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    for &m in &chained.multipliers {
        assert!((m - 1.0).abs() < 1e-9, "expected 1.0, got {m}");
    }
}

#[test]
fn test_compose_identity_multipliers_2d() {
    let c1 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    for &m in &chained.multipliers {
        assert!((m - 1.0).abs() < 1e-9, "expected 1.0, got {m}");
    }
}

#[test]
fn test_composed_multipliers_nonnegative_2d() {
    let c1 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    for (i, &m) in chained.multipliers.iter().enumerate() {
        assert!(m >= -1e-9, "multiplier[{i}] = {m} should be non-negative");
    }
}

#[test]
fn test_composed_multiplier_count_matches_input_rows() {
    let c1 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.multipliers.len(), c1.input_matrix.len());
}

#[test]
fn test_compose_3d_valid() {
    let c1 = build_simple_box_cert(3, &[0.0; 3], &[1.0; 3], &[0.0; 3], &[2.0; 3]);
    let c2 = build_simple_box_cert(3, &[0.0; 3], &[2.0; 3], &[0.0; 3], &[4.0; 3]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.multipliers.len(), 6); // 2*3 = 6 rows
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_compose_produces_valid_cert_2d_symmetric() {
    let c1 = build_simple_box_cert(2, &[-1.0, -1.0], &[1.0, 1.0], &[-2.0, -2.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[-2.0, -2.0], &[2.0, 2.0], &[-3.0, -3.0], &[3.0, 3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_compose_multiplier_length_equals_cert1_input_len() {
    let c1 = build_simple_box_cert(3, &[0.0; 3], &[1.0; 3], &[0.0; 3], &[2.0; 3]);
    let c2 = build_simple_box_cert(3, &[0.0; 3], &[2.0; 3], &[0.0; 3], &[5.0; 3]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.multipliers.len(), c1.input_matrix.len());
}

#[test]
fn test_compose_1d_multiplier_count() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[4.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.multipliers.len(), 2); // 2*1 = 2 rows for 1D box
}

// --- Edge cases ---

#[test]
fn test_chain_empty_constraints_returns_empty_cert() {
    // 0-dimensional certs: compose_multipliers must not divide by zero.
    // Both certs are vacuously valid; the chained cert should also be empty.
    let c1 = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let chained =
        chain_farkas_certs(&c1, &c1.clone()).expect("chaining empty certs should succeed");
    assert!(chained.multipliers.is_empty());
    assert!(chained.input_matrix.is_empty());
    assert!(chained.output_matrix.is_empty());
    assert_eq!(chained.input_dim, 0);
    assert_eq!(chained.output_dim, 0);
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_empty_cert1_output_nonempty_cert2_input() {
    // cert1 has empty output but cert2 has empty input (matching): should succeed.
    let c1 = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let c2 = c1.clone();
    let chained = chain_farkas_certs(&c1, &c2).expect("chaining two empty certs should succeed");
    assert!(chained.multipliers.is_empty());
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_single_dimension_structure() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[4.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_matrix.len(), 2);
    assert_eq!(chained.output_matrix.len(), 2);
}

#[test]
fn test_chain_large_10d() {
    let dim = 10;
    let lo = vec![0.0; dim];
    let hi1 = vec![1.0; dim];
    let hi2 = vec![2.0; dim];
    let hi3 = vec![4.0; dim];
    let c1 = build_simple_box_cert(dim, &lo, &hi1, &lo, &hi2);
    let c2 = build_simple_box_cert(dim, &lo, &hi2, &lo, &hi3);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, dim);
    assert_eq!(chained.multipliers.len(), 2 * dim);
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_exact_interface_match() {
    let c1 = build_simple_box_cert(1, &[-1.0], &[1.0], &[-2.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[-2.0], &[2.0], &[-3.0], &[3.0]);
    assert!(chain_farkas_certs(&c1, &c2).is_ok());
}

#[test]
fn test_chain_interface_within_epsilon_passes() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    // Perturb less than EPSILON (1e-9)
    c2.input_bounds[0] += 1e-12;
    c2.input_bounds[1] -= 1e-12;
    c2.input_matrix[0][0] += 1e-12;
    assert_eq!(verify_farkas_certificate(&c2), FarkasVerifyResult::Valid);
    assert!(chain_farkas_certs(&c1, &c2).is_ok());
}

#[test]
fn test_chain_interface_beyond_epsilon_fails() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    c2.input_bounds[0] += 1e-6; // > EPSILON
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InterfaceMismatch));
}

#[test]
fn test_chain_negative_bounds() {
    let c1 = build_simple_box_cert(1, &[-10.0], &[-5.0], &[-12.0], &[-3.0]);
    let c2 = build_simple_box_cert(1, &[-12.0], &[-3.0], &[-15.0], &[0.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_bounds, c1.input_bounds);
    assert_eq!(chained.output_bounds, c2.output_bounds);
}

#[test]
fn test_chain_wide_bounds() {
    let c1 = build_simple_box_cert(1, &[-1000.0], &[1000.0], &[-2000.0], &[2000.0]);
    let c2 = build_simple_box_cert(1, &[-2000.0], &[2000.0], &[-5000.0], &[5000.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_tight_bounds() {
    let c1 = build_simple_box_cert(1, &[0.999], &[1.001], &[0.998], &[1.002]);
    let c2 = build_simple_box_cert(1, &[0.998], &[1.002], &[0.997], &[1.003]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

// --- Soundness verification ---

#[test]
fn test_chain_containment_a_to_c() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, c1.input_dim);
    assert_eq!(chained.output_dim, c2.output_dim);
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_input_from_cert1_output_from_cert2() {
    let c1 = build_simple_box_cert(1, &[1.0], &[3.0], &[0.0], &[4.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[4.0], &[-2.0], &[6.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_bounds, c1.input_bounds);
    assert_eq!(chained.output_bounds, c2.output_bounds);
}

#[test]
fn test_three_way_chaining_1d() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let c3 = build_simple_box_cert(1, &[0.0], &[3.0], &[0.0], &[4.0]);
    let c12 = chain_farkas_certs(&c1, &c2).unwrap();
    let c123 = chain_farkas_certs(&c12, &c3).unwrap();
    assert_eq!(verify_farkas_certificate(&c123), FarkasVerifyResult::Valid);
    assert_eq!(c123.input_bounds, c1.input_bounds);
    assert_eq!(c123.output_bounds, c3.output_bounds);
}

#[test]
fn test_three_way_chaining_2d() {
    let c1 = build_simple_box_cert(2, &[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[2.0, 2.0]);
    let c2 = build_simple_box_cert(2, &[0.0, 0.0], &[2.0, 2.0], &[0.0, 0.0], &[3.0, 3.0]);
    let c3 = build_simple_box_cert(2, &[0.0, 0.0], &[3.0, 3.0], &[0.0, 0.0], &[4.0, 4.0]);
    let c12 = chain_farkas_certs(&c1, &c2).unwrap();
    let c123 = chain_farkas_certs(&c12, &c3).unwrap();
    assert_eq!(verify_farkas_certificate(&c123), FarkasVerifyResult::Valid);
    assert_eq!(c123.input_dim, 2);
    assert_eq!(c123.output_dim, 2);
}

#[test]
fn test_chain_preserves_box_structure_2d() {
    let c1 = build_simple_box_cert(2, &[-1.0, 0.0], &[1.0, 2.0], &[-2.0, -1.0], &[2.0, 3.0]);
    let c2 = build_simple_box_cert(2, &[-2.0, -1.0], &[2.0, 3.0], &[-3.0, -2.0], &[3.0, 4.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_matrix.len(), 4); // 2*dim
    assert_eq!(chained.output_matrix.len(), 4);
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_mixed_positive_negative_bounds() {
    let c1 = build_simple_box_cert(1, &[-5.0], &[5.0], &[-10.0], &[10.0]);
    let c2 = build_simple_box_cert(1, &[-10.0], &[10.0], &[-20.0], &[20.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
    assert_eq!(chained.input_bounds, c1.input_bounds);
    assert_eq!(chained.output_bounds, c2.output_bounds);
}

#[test]
fn test_chain_idempotent_same_cert() {
    let c = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[2.0]);
    let chained = chain_farkas_certs(&c, &c).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
    assert_eq!(chained.input_bounds, c.input_bounds);
    assert_eq!(chained.output_bounds, c.output_bounds);
}

#[test]
fn test_chain_four_way_chaining() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let c3 = build_simple_box_cert(1, &[0.0], &[3.0], &[0.0], &[4.0]);
    let c4 = build_simple_box_cert(1, &[0.0], &[4.0], &[0.0], &[5.0]);
    let c12 = chain_farkas_certs(&c1, &c2).unwrap();
    let c123 = chain_farkas_certs(&c12, &c3).unwrap();
    let c1234 = chain_farkas_certs(&c123, &c4).unwrap();
    assert_eq!(verify_farkas_certificate(&c1234), FarkasVerifyResult::Valid);
    assert_eq!(c1234.input_bounds, c1.input_bounds);
    assert_eq!(c1234.output_bounds, c4.output_bounds);
}

#[test]
fn test_chain_cert1_dimension_error_is_invalid() {
    let mut c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    c1.input_matrix[0] = vec![1.0, 2.0]; // wrong column count
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_chain_cert2_constraint_mismatch_is_invalid() {
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let mut c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    // Make output bound tighter than weighted input bound can achieve
    c2.output_bounds[0] = -100.0;
    let err = chain_farkas_certs(&c1, &c2).unwrap_err();
    assert!(matches!(err, FarkasBridgeError::InvalidCertificate(_)));
}

#[test]
fn test_chain_fractional_bounds() {
    let c1 = build_simple_box_cert(1, &[0.25], &[0.75], &[0.1], &[0.9]);
    let c2 = build_simple_box_cert(1, &[0.1], &[0.9], &[0.0], &[1.0]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

// --- Divide-by-zero edge cases (#3211) ---

#[test]
fn test_compose_empty_output_no_divide_by_zero() {
    // Regression: compose_multipliers must not divide by zero when
    // output_matrix is empty. This is the original #3211 scenario.
    let empty = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    // Should not panic.
    let result = chain_farkas_certs(&empty, &empty).expect("empty certs should chain");
    assert!(result.multipliers.is_empty());
    assert_eq!(
        verify_farkas_certificate(&result),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_compose_empty_certs_multipliers_are_empty() {
    // When both certs have empty output (cert2_num_out == 0), the composed
    // multipliers must be empty (not zero-filled), otherwise the result fails
    // verification: num_out==0 requires multipliers.is_empty().
    let empty = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let result = chain_farkas_certs(&empty, &empty).unwrap();
    assert!(
        result.multipliers.is_empty(),
        "composed multipliers should be empty when cert2 output is empty, got len={}",
        result.multipliers.len()
    );
}

#[test]
fn test_chain_empty_cert_result_passes_verification() {
    // The composed certificate from two empty certs must itself be verifiable.
    let empty = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let result = chain_farkas_certs(&empty, &empty).unwrap();
    assert_eq!(
        verify_farkas_certificate(&result),
        FarkasVerifyResult::Valid,
        "composed empty cert must pass verification"
    );
}

#[test]
fn test_chain_single_output_row_no_panic() {
    // Single output constraint: block_size = 2/1 = 2 (no division issue,
    // but tests the boundary between 0 and >0 output rows).
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    // 1D box: 2 output rows (upper + lower), 2 input rows each.
    assert_eq!(c1.output_matrix.len(), 2);
    assert_eq!(c2.input_matrix.len(), 2);
    let result = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(
        verify_farkas_certificate(&result),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_chain_zero_dim_certs_dimensions_preserved() {
    // 0-dimensional certs should produce a 0-dimensional result.
    let empty = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let result = chain_farkas_certs(&empty, &empty).unwrap();
    assert_eq!(result.input_dim, 0);
    assert_eq!(result.output_dim, 0);
    assert!(result.input_matrix.is_empty());
    assert!(result.output_matrix.is_empty());
    assert!(result.input_bounds.is_empty());
    assert!(result.output_bounds.is_empty());
}

#[test]
fn test_chain_five_way_chaining_valid() {
    // Stress test: 5-way chaining to ensure no accumulation errors.
    let c1 = build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[2.0]);
    let c2 = build_simple_box_cert(1, &[0.0], &[2.0], &[0.0], &[3.0]);
    let c3 = build_simple_box_cert(1, &[0.0], &[3.0], &[0.0], &[4.0]);
    let c4 = build_simple_box_cert(1, &[0.0], &[4.0], &[0.0], &[5.0]);
    let c5 = build_simple_box_cert(1, &[0.0], &[5.0], &[0.0], &[6.0]);
    let c12 = chain_farkas_certs(&c1, &c2).unwrap();
    let c123 = chain_farkas_certs(&c12, &c3).unwrap();
    let c1234 = chain_farkas_certs(&c123, &c4).unwrap();
    let c12345 = chain_farkas_certs(&c1234, &c5).unwrap();
    assert_eq!(
        verify_farkas_certificate(&c12345),
        FarkasVerifyResult::Valid
    );
    assert_eq!(c12345.input_bounds, c1.input_bounds);
    assert_eq!(c12345.output_bounds, c5.output_bounds);
}

#[test]
fn test_chain_large_20d_no_panic() {
    // Large dimension: 20D box certs, 40 constraints each.
    let dim = 20;
    let lo = vec![0.0; dim];
    let hi1 = vec![1.0; dim];
    let hi2 = vec![2.0; dim];
    let hi3 = vec![4.0; dim];
    let c1 = build_simple_box_cert(dim, &lo, &hi1, &lo, &hi2);
    let c2 = build_simple_box_cert(dim, &lo, &hi2, &lo, &hi3);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    assert_eq!(chained.input_dim, dim);
    assert_eq!(chained.output_dim, dim);
    assert_eq!(chained.multipliers.len(), 2 * dim);
    assert_eq!(
        verify_farkas_certificate(&chained),
        FarkasVerifyResult::Valid
    );
}

#[test]
fn test_compose_multipliers_all_nonnegative_3d() {
    // All composed multipliers should be non-negative for valid box certs.
    let c1 = build_simple_box_cert(3, &[-1.0; 3], &[1.0; 3], &[-2.0; 3], &[2.0; 3]);
    let c2 = build_simple_box_cert(3, &[-2.0; 3], &[2.0; 3], &[-3.0; 3], &[3.0; 3]);
    let chained = chain_farkas_certs(&c1, &c2).unwrap();
    for (i, &m) in chained.multipliers.iter().enumerate() {
        assert!(m >= -1e-9, "multiplier[{i}] = {m} should be non-negative");
    }
}
