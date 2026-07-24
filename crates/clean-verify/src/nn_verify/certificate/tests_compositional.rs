// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for compositional certificate verification.

use super::compositional::{
    certificate_summary, compose_block_certificates, compute_certificate_trust_level,
    verify_block_certificate, verify_dimensional_consistency, verify_skip_connection,
    BlockCertificate, TrustLevel,
};

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

/// Build a valid 2D block certificate with identity-like constraints.
///
/// Constraint system: 2 constraints (one per input dim), identity matrix,
/// RHS = upper bounds. Multipliers are a single row of ones.
fn make_valid_block(
    block_id: usize,
    input_bounds: Vec<(f64, f64)>,
    output_bounds: Vec<(f64, f64)>,
    layer_count: usize,
) -> BlockCertificate {
    let dim = input_bounds.len();
    // Identity constraint matrix.
    let constraints: Vec<Vec<f64>> = (0..dim)
        .map(|i| {
            let mut row = vec![0.0; dim];
            row[i] = 1.0;
            row
        })
        .collect();
    let rhs: Vec<f64> = input_bounds.iter().map(|&(_, hi)| hi).collect();
    // One multiplier row (all 1.0) matching the constraint count.
    let farkas_multipliers = vec![vec![1.0; dim]];

    BlockCertificate {
        block_id,
        input_bounds,
        output_bounds,
        layer_count,
        farkas_multipliers,
        constraints,
        rhs,
    }
}

/// Build a block certificate with explicitly negative Farkas multipliers.
fn make_invalid_negative_multiplier_block(block_id: usize) -> BlockCertificate {
    BlockCertificate {
        block_id,
        input_bounds: vec![(0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0)],
        layer_count: 1,
        farkas_multipliers: vec![vec![-0.5]],
        constraints: vec![vec![1.0]],
        rhs: vec![1.0],
    }
}

/// Build a block with mismatched constraint/rhs dimensions.
fn make_dim_mismatch_block(block_id: usize) -> BlockCertificate {
    BlockCertificate {
        block_id,
        input_bounds: vec![(0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0)],
        layer_count: 1,
        farkas_multipliers: vec![vec![1.0, 1.0]],
        constraints: vec![vec![1.0], vec![1.0]],
        rhs: vec![1.0], // mismatched: 2 constraints but 1 rhs
    }
}

// ---------------------------------------------------------------------------
// verify_block_certificate tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_block_valid_1d() {
    let block = make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1);
    let result = verify_block_certificate(&block);
    assert!(result.valid, "errors: {:?}", result.errors);
    assert_eq!(result.block_id, 0);
    assert!(result.errors.is_empty());
}

#[test]
fn test_verify_block_valid_2d() {
    let block = make_valid_block(
        1,
        vec![(0.0, 1.0), (-1.0, 1.0)],
        vec![(0.0, 2.0), (-2.0, 2.0)],
        2,
    );
    let result = verify_block_certificate(&block);
    assert!(result.valid, "errors: {:?}", result.errors);
}

#[test]
fn test_verify_block_valid_3d() {
    let block = make_valid_block(
        2,
        vec![(0.0, 1.0), (0.0, 2.0), (0.0, 3.0)],
        vec![(0.0, 1.5), (0.0, 2.5), (0.0, 3.5)],
        3,
    );
    let result = verify_block_certificate(&block);
    assert!(result.valid, "errors: {:?}", result.errors);
}

#[test]
fn test_verify_block_negative_multiplier() {
    let block = make_invalid_negative_multiplier_block(0);
    let result = verify_block_certificate(&block);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("negative")),
        "expected negative multiplier error, got: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_block_constraint_rhs_mismatch() {
    let block = make_dim_mismatch_block(0);
    let result = verify_block_certificate(&block);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("constraint rows")),
        "expected constraint/rhs mismatch error, got: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_block_multiplier_row_length_mismatch() {
    let block = BlockCertificate {
        block_id: 0,
        input_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0)],
        layer_count: 1,
        farkas_multipliers: vec![vec![1.0]], // 1 element but 2 constraints
        constraints: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
        rhs: vec![1.0, 1.0],
    };
    let result = verify_block_certificate(&block);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("multiplier row")),
        "expected multiplier row length error, got: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_block_constraint_col_mismatch() {
    let block = BlockCertificate {
        block_id: 0,
        input_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0)],
        layer_count: 1,
        farkas_multipliers: vec![vec![1.0]],
        constraints: vec![vec![1.0, 0.0, 0.0]], // 3 cols but input_bounds has 2 dims
        rhs: vec![1.0],
    };
    let result = verify_block_certificate(&block);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("cols")),
        "expected column mismatch error, got: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_block_preserves_block_id() {
    let block = make_valid_block(42, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1);
    let result = verify_block_certificate(&block);
    assert_eq!(result.block_id, 42);
}

// ---------------------------------------------------------------------------
// compose_block_certificates tests
// ---------------------------------------------------------------------------

#[test]
fn test_compose_empty_chain() {
    let result = compose_block_certificates(&[]);
    assert!(result.valid);
    assert_eq!(result.chain_length, 0);
    assert!(result.failures.is_empty());
}

#[test]
fn test_compose_single_block() {
    let blocks = [make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1)];
    let result = compose_block_certificates(&blocks);
    assert!(result.valid);
    assert_eq!(result.chain_length, 1);
}

#[test]
fn test_compose_two_blocks_matching_intervals() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(result.valid, "failures: {:?}", result.failures);
    assert_eq!(result.chain_length, 2);
}

#[test]
fn test_compose_two_blocks_subset_intervals() {
    // Block 0 output [0.1, 1.9] ⊆ Block 1 input [0.0, 2.0]
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.1, 1.9)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(result.valid, "failures: {:?}", result.failures);
}

#[test]
fn test_compose_two_blocks_mismatching_intervals() {
    // Block 0 output [0, 3] NOT ⊆ Block 1 input [0, 2]
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 3.0)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 4.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(!result.valid);
    assert!(!result.failures.is_empty());
}

#[test]
fn test_compose_two_blocks_dimension_mismatch() {
    // Block 0 has 2D output, Block 1 has 1D input.
    let blocks = [
        make_valid_block(
            0,
            vec![(0.0, 1.0), (0.0, 1.0)],
            vec![(0.0, 2.0), (0.0, 2.0)],
            1,
        ),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(!result.valid);
    assert!(
        result.failures.iter().any(|(_, msg)| msg.contains("dim")),
        "expected dimension mismatch, got: {:?}",
        result.failures
    );
}

#[test]
fn test_compose_three_block_chain() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
        make_valid_block(2, vec![(0.0, 3.0)], vec![(0.0, 4.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(result.valid, "failures: {:?}", result.failures);
    assert_eq!(result.chain_length, 3);
}

#[test]
fn test_compose_failure_at_second_junction() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 5.0)], 1),
        // Block 2 input [0, 3] does not contain block 1 output [0, 5].
        make_valid_block(2, vec![(0.0, 3.0)], vec![(0.0, 6.0)], 1),
    ];
    let result = compose_block_certificates(&blocks);
    assert!(!result.valid);
    // The failure is at junction index 1 (between blocks 1 and 2).
    assert!(
        result.failures.iter().any(|&(idx, _)| idx == 1),
        "expected failure at junction 1, got: {:?}",
        result.failures
    );
}

// ---------------------------------------------------------------------------
// verify_skip_connection tests
// ---------------------------------------------------------------------------

#[test]
fn test_skip_connection_valid() {
    let main = make_valid_block(0, vec![(0.0, 1.0)], vec![(1.0, 2.0)], 1);
    let skip = make_valid_block(1, vec![(0.0, 1.0)], vec![(0.5, 1.5)], 1);
    // main + skip: [1.5, 3.5], combined must contain this.
    let combined = vec![(1.5, 3.5)];
    assert!(verify_skip_connection(&main, &skip, &combined));
}

#[test]
fn test_skip_connection_wider_combined() {
    let main = make_valid_block(0, vec![(0.0, 1.0)], vec![(1.0, 2.0)], 1);
    let skip = make_valid_block(1, vec![(0.0, 1.0)], vec![(0.5, 1.5)], 1);
    // Wider combined: [1.0, 4.0] ⊇ [1.5, 3.5]
    let combined = vec![(1.0, 4.0)];
    assert!(verify_skip_connection(&main, &skip, &combined));
}

#[test]
fn test_skip_connection_too_narrow() {
    let main = make_valid_block(0, vec![(0.0, 1.0)], vec![(1.0, 2.0)], 1);
    let skip = make_valid_block(1, vec![(0.0, 1.0)], vec![(0.5, 1.5)], 1);
    // Too narrow: [2.0, 3.0] does not contain [1.5, 3.5]
    let combined = vec![(2.0, 3.0)];
    assert!(!verify_skip_connection(&main, &skip, &combined));
}

#[test]
fn test_skip_connection_dimension_mismatch_main_skip() {
    let main = make_valid_block(0, vec![(0.0, 1.0)], vec![(1.0, 2.0)], 1);
    let skip = make_valid_block(
        1,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(0.5, 1.5), (0.5, 1.5)],
        1,
    );
    let combined = vec![(1.5, 3.5)];
    assert!(!verify_skip_connection(&main, &skip, &combined));
}

#[test]
fn test_skip_connection_dimension_mismatch_combined() {
    let main = make_valid_block(0, vec![(0.0, 1.0)], vec![(1.0, 2.0)], 1);
    let skip = make_valid_block(1, vec![(0.0, 1.0)], vec![(0.5, 1.5)], 1);
    // Combined has 2 dims, main/skip have 1 dim.
    let combined = vec![(1.5, 3.5), (0.0, 1.0)];
    assert!(!verify_skip_connection(&main, &skip, &combined));
}

#[test]
fn test_skip_connection_2d_valid() {
    let main = make_valid_block(
        0,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(1.0, 2.0), (0.0, 1.0)],
        1,
    );
    let skip = make_valid_block(
        1,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(0.5, 1.5), (0.5, 1.5)],
        1,
    );
    // dim0: [1.5, 3.5], dim1: [0.5, 2.5]
    let combined = vec![(1.5, 3.5), (0.5, 2.5)];
    assert!(verify_skip_connection(&main, &skip, &combined));
}

// ---------------------------------------------------------------------------
// compute_certificate_trust_level tests
// ---------------------------------------------------------------------------

#[test]
fn test_trust_level_empty() {
    assert_eq!(compute_certificate_trust_level(&[]), TrustLevel::Unverified);
}

#[test]
fn test_trust_level_all_valid() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
    ];
    assert_eq!(
        compute_certificate_trust_level(&blocks),
        TrustLevel::FullyVerified
    );
}

#[test]
fn test_trust_level_all_invalid() {
    let blocks = [
        make_invalid_negative_multiplier_block(0),
        make_invalid_negative_multiplier_block(1),
    ];
    assert_eq!(
        compute_certificate_trust_level(&blocks),
        TrustLevel::Unverified
    );
}

#[test]
fn test_trust_level_partial() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1),
        make_invalid_negative_multiplier_block(1),
    ];
    assert_eq!(
        compute_certificate_trust_level(&blocks),
        TrustLevel::PartiallyVerified {
            verified_blocks: 1,
            total_blocks: 2,
        }
    );
}

#[test]
fn test_trust_level_single_valid() {
    let blocks = [make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1)];
    assert_eq!(
        compute_certificate_trust_level(&blocks),
        TrustLevel::FullyVerified
    );
}

#[test]
fn test_trust_level_single_invalid() {
    let blocks = [make_invalid_negative_multiplier_block(0)];
    assert_eq!(
        compute_certificate_trust_level(&blocks),
        TrustLevel::Unverified
    );
}

// ---------------------------------------------------------------------------
// verify_dimensional_consistency tests
// ---------------------------------------------------------------------------

#[test]
fn test_dim_consistency_empty() {
    let result = verify_dimensional_consistency(&[]);
    assert!(result.consistent);
    assert!(result.mismatches.is_empty());
}

#[test]
fn test_dim_consistency_single_block() {
    let blocks = [make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0)], 1)];
    let result = verify_dimensional_consistency(&blocks);
    assert!(result.consistent);
}

#[test]
fn test_dim_consistency_matching_chain() {
    let blocks = [
        make_valid_block(
            0,
            vec![(0.0, 1.0), (0.0, 1.0)],
            vec![(0.0, 2.0), (0.0, 2.0)],
            1,
        ),
        make_valid_block(
            1,
            vec![(0.0, 2.0), (0.0, 2.0)],
            vec![(0.0, 3.0), (0.0, 3.0)],
            1,
        ),
    ];
    let result = verify_dimensional_consistency(&blocks);
    assert!(result.consistent);
}

#[test]
fn test_dim_consistency_mismatch() {
    let blocks = [
        make_valid_block(
            0,
            vec![(0.0, 1.0), (0.0, 1.0)],
            vec![(0.0, 2.0), (0.0, 2.0)],
            1,
        ),
        make_valid_block(1, vec![(0.0, 2.0)], vec![(0.0, 3.0)], 1),
    ];
    let result = verify_dimensional_consistency(&blocks);
    assert!(!result.consistent);
    assert_eq!(result.mismatches.len(), 1);
    let (idx, expected, actual) = result.mismatches[0];
    assert_eq!(idx, 0);
    assert_eq!(expected, 2); // block 0 output dim
    assert_eq!(actual, 1); // block 1 input dim
}

#[test]
fn test_dim_consistency_multiple_mismatches() {
    let blocks = [
        make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 2.0), (0.0, 2.0)], 1),
        make_valid_block(
            1,
            vec![(0.0, 2.0)],
            vec![(0.0, 3.0), (0.0, 3.0), (0.0, 3.0)],
            1,
        ),
        make_valid_block(2, vec![(0.0, 3.0)], vec![(0.0, 4.0)], 1),
    ];
    let result = verify_dimensional_consistency(&blocks);
    assert!(!result.consistent);
    assert_eq!(result.mismatches.len(), 2);
}

// ---------------------------------------------------------------------------
// certificate_summary tests
// ---------------------------------------------------------------------------

#[test]
fn test_summary_empty() {
    let summary = certificate_summary(&[]);
    assert_eq!(summary.num_blocks, 0);
    assert_eq!(summary.total_layers, 0);
    assert_eq!(summary.total_multipliers, 0);
    assert_eq!(summary.max_bound_width, 0.0);
}

#[test]
fn test_summary_single_block() {
    let blocks = [make_valid_block(0, vec![(0.0, 1.0)], vec![(0.0, 3.0)], 2)];
    let summary = certificate_summary(&blocks);
    assert_eq!(summary.num_blocks, 1);
    assert_eq!(summary.total_layers, 2);
    assert_eq!(summary.total_multipliers, 1); // 1 row * 1 col
    assert!((summary.max_bound_width - 3.0).abs() < 1e-12);
}

#[test]
fn test_summary_multiple_blocks() {
    let blocks = [
        make_valid_block(
            0,
            vec![(0.0, 1.0), (0.0, 2.0)],
            vec![(0.0, 3.0), (0.0, 4.0)],
            3,
        ),
        make_valid_block(
            1,
            vec![(0.0, 3.0), (0.0, 4.0)],
            vec![(0.0, 5.0), (0.0, 10.0)],
            2,
        ),
    ];
    let summary = certificate_summary(&blocks);
    assert_eq!(summary.num_blocks, 2);
    assert_eq!(summary.total_layers, 5); // 3 + 2
    assert_eq!(summary.total_multipliers, 4); // 2 + 2 (1 row * 2 cols each)
    assert!((summary.max_bound_width - 10.0).abs() < 1e-12);
}

#[test]
fn test_summary_max_width_from_input() {
    // Input bound is wider than output bound.
    let blocks = [make_valid_block(0, vec![(-5.0, 5.0)], vec![(0.0, 1.0)], 1)];
    let summary = certificate_summary(&blocks);
    assert!((summary.max_bound_width - 10.0).abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// Proof status tracking
// ---------------------------------------------------------------------------

#[test]
fn test_proof_status_constants() {
    use super::compositional::{T75_COMPOSITIONAL_SOUNDNESS, T76_SKIP_CONNECTION_SOUNDNESS};
    use crate::spec::ProofStatus;
    assert!(matches!(
        T75_COMPOSITIONAL_SOUNDNESS,
        ProofStatus::DerivedPending
    ));
    assert!(matches!(
        T76_SKIP_CONNECTION_SOUNDNESS,
        ProofStatus::DerivedPending
    ));
}
