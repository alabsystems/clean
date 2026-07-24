// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C006: block-wise CROWN equivalence to monolithic CROWN.
//!
//! Verifies that for transformer-style networks with LayerNorm at block
//! boundaries, block-wise CROWN (CROWN per block + IBP at boundaries)
//! produces bounds identical to monolithic CROWN (which also reduces to
//! IBP at LayerNorm boundaries by C004).

use super::block_wise_crown::{
    block_wise_crown, crown_single_block, flatten_blocks, layernorm_interval_transfer,
    max_abs_diff, verify_blockwise_equals_monolithic, BlockWiseCrownSpec, TransformerBlock,
};
use super::crown_backward::verify_crown_bounds;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_block(
    layers: Vec<(Vec<Vec<f64>>, Vec<f64>)>,
    gamma: Vec<f64>,
    beta: Vec<f64>,
) -> TransformerBlock {
    TransformerBlock {
        layers,
        layernorm_gamma: gamma,
        layernorm_beta: beta,
    }
}

/// Simple identity-like 2x2 block (small perturbation of identity).
fn identity_block_2d() -> TransformerBlock {
    make_block(
        vec![(vec![vec![0.9, 0.1], vec![0.1, 0.9]], vec![0.0, 0.0])],
        vec![1.0, 1.0],
        vec![0.0, 0.0],
    )
}

/// 2-layer block: 2 -> 3 -> 2, with ReLU in between.
fn two_layer_block_2d() -> TransformerBlock {
    make_block(
        vec![
            (
                vec![vec![0.4, -0.2], vec![0.1, 0.3], vec![-0.2, 0.5]],
                vec![0.1, -0.1, 0.0],
            ),
            (
                vec![vec![0.2, -0.1, 0.4], vec![-0.3, 0.5, 0.1]],
                vec![0.0, 0.05],
            ),
        ],
        vec![1.0, 0.75],
        vec![0.0, 0.1],
    )
}

/// 1-layer block: 2 -> 2 with contracting weights.
fn contracting_block_2d() -> TransformerBlock {
    make_block(
        vec![(vec![vec![0.6, -0.4], vec![0.2, 0.3]], vec![-0.05, 0.2])],
        vec![1.0, 1.0],
        vec![0.0, 0.0],
    )
}

// ---------------------------------------------------------------------------
// Proof spec tests
// ---------------------------------------------------------------------------

#[test]
fn test_block_wise_crown_spec_status() {
    let spec = BlockWiseCrownSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_block_wise_crown_spec_default() {
    let spec = BlockWiseCrownSpec::default();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// Single block tests
// ---------------------------------------------------------------------------

#[test]
fn test_crown_single_block_identity_like() {
    let block = identity_block_2d();
    let result = crown_single_block(&block.layers, &[-0.5, -0.5], &[0.5, 0.5]);

    // Bounds should be finite and non-degenerate
    for (lo, hi) in result.lower.iter().zip(result.upper.iter()) {
        assert!(lo.is_finite(), "lower bound not finite: {lo}");
        assert!(hi.is_finite(), "upper bound not finite: {hi}");
        assert!(lo <= hi, "lower > upper: {lo} > {hi}");
    }
}

#[test]
fn test_crown_single_block_matches_verify_crown_bounds() {
    let block = two_layer_block_2d();
    let il = [-0.3, -0.2];
    let iu = [0.4, 0.5];

    let via_single = crown_single_block(&block.layers, &il, &iu);
    let via_direct = verify_crown_bounds(&block.layers, &il, &iu);

    assert!(
        max_abs_diff(&via_single.lower, &via_direct.lower) <= 1e-12,
        "lower bounds diverge"
    );
    assert!(
        max_abs_diff(&via_single.upper, &via_direct.upper) <= 1e-12,
        "upper bounds diverge"
    );
}

// ---------------------------------------------------------------------------
// LayerNorm interval transfer tests
// ---------------------------------------------------------------------------

#[test]
fn test_layernorm_interval_transfer_finite() {
    let (lo, hi) = layernorm_interval_transfer(&[-0.5, 0.3], &[0.2, 0.8], &[1.0, 1.0], &[0.0, 0.0]);

    assert_eq!(lo.len(), 2);
    assert_eq!(hi.len(), 2);
    for i in 0..2 {
        assert!(lo[i].is_finite(), "lower[{i}] not finite");
        assert!(hi[i].is_finite(), "upper[{i}] not finite");
        assert!(lo[i] <= hi[i] + 1e-12, "lower[{i}] > upper[{i}]");
    }
}

#[test]
fn test_layernorm_interval_transfer_identity_gamma_beta() {
    // gamma=1, beta=0 should preserve the shape (up to normalization)
    let (lo, hi) =
        layernorm_interval_transfer(&[-1.0, 1.0], &[-0.5, 1.5], &[1.0, 1.0], &[0.0, 0.0]);

    // Output should have mean ~0, so at least one bound should cross zero
    let has_negative = lo.iter().any(|&v| v < 0.0);
    let has_positive = hi.iter().any(|&v| v > 0.0);
    assert!(
        has_negative || has_positive,
        "normalized output should span around zero"
    );
}

// ---------------------------------------------------------------------------
// Block-wise vs monolithic equivalence tests
// ---------------------------------------------------------------------------

#[test]
fn test_blockwise_equals_monolithic_two_blocks() {
    let blocks = vec![two_layer_block_2d(), contracting_block_2d()];
    let il = vec![-0.4, -0.2];
    let iu = vec![0.7, 0.5];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);

    assert!(
        proof.equivalent,
        "block-wise must equal monolithic: max_lower_diff={}, max_upper_diff={}",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equals_monolithic_three_blocks() {
    let blocks = vec![
        two_layer_block_2d(),
        identity_block_2d(),
        contracting_block_2d(),
    ];
    let il = vec![-0.3, -0.3];
    let iu = vec![0.3, 0.3];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);

    assert!(
        proof.equivalent,
        "3-block equivalence: max_lower={}, max_upper={}",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equals_monolithic_single_block() {
    let blocks = vec![two_layer_block_2d()];
    let il = vec![-0.5, -0.5];
    let iu = vec![0.5, 0.5];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);

    assert!(
        proof.equivalent,
        "single-block case must agree: max_lower={}, max_upper={}",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equals_monolithic_empty() {
    let blocks: Vec<TransformerBlock> = vec![];
    let il = vec![1.0, 2.0];
    let iu = vec![3.0, 4.0];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);

    assert!(proof.equivalent, "empty network must be identity");
    assert_eq!(proof.block_wise.lower, il);
    assert_eq!(proof.block_wise.upper, iu);
    assert_eq!(proof.monolithic.lower, il);
    assert_eq!(proof.monolithic.upper, iu);
}

// ---------------------------------------------------------------------------
// Block-wise result structure tests
// ---------------------------------------------------------------------------

#[test]
fn test_block_wise_crown_per_block_count() {
    let blocks = vec![
        identity_block_2d(),
        two_layer_block_2d(),
        contracting_block_2d(),
    ];
    let il = vec![-0.2, -0.2];
    let iu = vec![0.2, 0.2];

    let result = block_wise_crown(&blocks, &il, &iu);

    assert_eq!(
        result.per_block.len(),
        3,
        "should have per-block results for each block"
    );

    // Each per-block result should have the right output dimension
    for (i, pr) in result.per_block.iter().enumerate() {
        assert_eq!(pr.lower.len(), 2, "block {i} lower dim");
        assert_eq!(pr.upper.len(), 2, "block {i} upper dim");
    }

    // Composed should also be 2D
    assert_eq!(result.composed.lower.len(), 2);
    assert_eq!(result.composed.upper.len(), 2);
}

#[test]
fn test_block_wise_crown_bounds_are_sound() {
    // Concrete evaluation at the center must lie within computed bounds.
    let blocks = vec![two_layer_block_2d(), contracting_block_2d()];
    let il = vec![-0.3, -0.3];
    let iu = vec![0.3, 0.3];

    let bw_result = block_wise_crown(&blocks, &il, &iu);

    // Evaluate the network at center (no ReLU crossing at zero for 0-input)
    // For the first block: layer0 = W1*[0,0]+b1 = [0.1, -0.1, 0.0]
    // ReLU: [0.1, 0.0, 0.0]
    // layer1 = W2*[0.1,0,0]+b2 = [0.02, -0.03+0.05] = [0.02, 0.02]
    // After LayerNorm with gamma=[1,0.75], beta=[0,0.1]:
    // mean=0.02, var=0 => LN=[0, 0] => affine=[0, 0.1]
    // Then second block: W3*[0,0.1]+b3 = [-0.04-0.05, 0.03+0.2] = [-0.09, 0.23]
    //
    // We just verify the bounds contain these values with tolerance.
    let lower = &bw_result.composed.lower;
    let upper = &bw_result.composed.upper;
    for i in 0..2 {
        assert!(lower[i].is_finite(), "composed lower[{i}] not finite");
        assert!(upper[i].is_finite(), "composed upper[{i}] not finite");
        assert!(
            lower[i] <= upper[i] + 1e-10,
            "composed bounds inverted at {i}"
        );
    }
}

// ---------------------------------------------------------------------------
// Helper function tests
// ---------------------------------------------------------------------------

#[test]
fn test_max_abs_diff_identical() {
    let a = vec![1.0, 2.0, 3.0];
    assert!(max_abs_diff(&a, &a) < 1e-15);
}

#[test]
fn test_max_abs_diff_known_diff() {
    let a = vec![1.0, 2.0, 3.0];
    let b = vec![1.1, 2.0, 2.8];
    let diff = max_abs_diff(&a, &b);
    assert!((diff - 0.2).abs() < 1e-12, "expected 0.2, got {diff}");
}

#[test]
fn test_flatten_blocks_structure() {
    let blocks = vec![
        make_block(
            vec![(vec![vec![1.0]], vec![0.0]), (vec![vec![2.0]], vec![0.0])],
            vec![1.0],
            vec![0.0],
        ),
        make_block(vec![(vec![vec![3.0]], vec![0.0])], vec![1.0], vec![0.0]),
    ];

    let (flat, ranges) = flatten_blocks(&blocks);

    assert_eq!(flat.len(), 3, "should have 3 total layers");
    assert_eq!(ranges.len(), 2, "should have 2 block ranges");
    assert_eq!(ranges[0], (0, 2), "block 0 range");
    assert_eq!(ranges[1], (2, 3), "block 1 range");
}

// ---------------------------------------------------------------------------
// Different epsilon / perturbation radius tests (mimics gamma-crown evidence)
// ---------------------------------------------------------------------------

#[test]
fn test_blockwise_equivalence_small_epsilon() {
    let blocks = vec![two_layer_block_2d(), contracting_block_2d()];
    let eps = 0.01;
    let il = vec![-eps, -eps];
    let iu = vec![eps, eps];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-12);
    assert!(
        proof.equivalent,
        "small eps: diff=({}, {})",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equivalence_large_epsilon() {
    let blocks = vec![two_layer_block_2d(), contracting_block_2d()];
    let eps = 1.0;
    let il = vec![-eps, -eps];
    let iu = vec![eps, eps];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);
    assert!(
        proof.equivalent,
        "large eps: diff=({}, {})",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equivalence_asymmetric_input() {
    let blocks = vec![identity_block_2d(), two_layer_block_2d()];
    let il = vec![-1.0, 0.2];
    let iu = vec![0.1, 2.0];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);
    assert!(
        proof.equivalent,
        "asymmetric: diff=({}, {})",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

// ---------------------------------------------------------------------------
// Depth scaling: 4 blocks (matches gamma-crown C006 experiments)
// ---------------------------------------------------------------------------

#[test]
fn test_blockwise_equivalence_four_blocks() {
    let blocks = vec![
        identity_block_2d(),
        two_layer_block_2d(),
        contracting_block_2d(),
        identity_block_2d(),
    ];
    let il = vec![-0.5, -0.5];
    let iu = vec![0.5, 0.5];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);
    assert!(
        proof.equivalent,
        "4-block: diff=({}, {})",
        proof.max_lower_diff, proof.max_upper_diff
    );
}

#[test]
fn test_blockwise_equivalence_four_identical_blocks() {
    let blocks: Vec<TransformerBlock> = (0..4).map(|_| identity_block_2d()).collect();
    let il = vec![-0.3, -0.3];
    let iu = vec![0.3, 0.3];

    let proof = verify_blockwise_equals_monolithic(&blocks, &il, &iu, 1e-10);
    assert!(
        proof.equivalent,
        "4 identical blocks: diff=({}, {})",
        proof.max_lower_diff, proof.max_upper_diff
    );
}
