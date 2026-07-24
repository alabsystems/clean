// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for multi-head attention bound verification (T55-T56).

use super::multi_head::*;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// split_heads
// ---------------------------------------------------------------------------

#[test]
fn test_split_heads_basic_2_heads() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 3,
        seq_len: 1,
    };
    let input: Vec<(f64, f64)> = vec![
        (0.0, 1.0),
        (1.0, 2.0),
        (2.0, 3.0),
        (3.0, 4.0),
        (4.0, 5.0),
        (5.0, 6.0),
    ];
    let heads = split_heads(&input, &config);
    assert_eq!(heads.len(), 2);
    assert_eq!(heads[0], vec![(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]);
    assert_eq!(heads[1], vec![(3.0, 4.0), (4.0, 5.0), (5.0, 6.0)]);
}

#[test]
fn test_split_heads_single_head() {
    let config = MultiHeadConfig {
        num_heads: 1,
        head_dim: 4,
        seq_len: 1,
    };
    let input: Vec<(f64, f64)> = vec![(0.0, 1.0), (1.0, 2.0), (2.0, 3.0), (3.0, 4.0)];
    let heads = split_heads(&input, &config);
    assert_eq!(heads.len(), 1);
    assert_eq!(heads[0].len(), 4);
}

#[test]
fn test_split_heads_four_heads() {
    let config = MultiHeadConfig {
        num_heads: 4,
        head_dim: 2,
        seq_len: 1,
    };
    let input: Vec<(f64, f64)> = (0..8).map(|i| (i as f64, i as f64 + 1.0)).collect();
    let heads = split_heads(&input, &config);
    assert_eq!(heads.len(), 4);
    for head in &heads {
        assert_eq!(head.len(), 2);
    }
    assert_eq!(heads[0][0], (0.0, 1.0));
    assert_eq!(heads[3][1], (7.0, 8.0));
}

#[test]
fn test_split_heads_single_dim_per_head() {
    let config = MultiHeadConfig {
        num_heads: 3,
        head_dim: 1,
        seq_len: 1,
    };
    let input = vec![(1.0, 2.0), (3.0, 4.0), (5.0, 6.0)];
    let heads = split_heads(&input, &config);
    assert_eq!(heads.len(), 3);
    assert_eq!(heads[0], vec![(1.0, 2.0)]);
    assert_eq!(heads[1], vec![(3.0, 4.0)]);
    assert_eq!(heads[2], vec![(5.0, 6.0)]);
}

#[test]
#[should_panic(expected = "input length")]
fn test_split_heads_length_mismatch_panics() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 3,
        seq_len: 1,
    };
    let input = vec![(0.0, 1.0); 5]; // 5 != 2*3
    let _ = split_heads(&input, &config);
}

// ---------------------------------------------------------------------------
// verify_head_independence
// ---------------------------------------------------------------------------

#[test]
fn test_head_independence_valid_uniform() {
    let heads = vec![vec![(0.0, 1.0), (1.0, 2.0)], vec![(2.0, 3.0), (3.0, 4.0)]];
    assert!(verify_head_independence(&heads));
}

#[test]
fn test_head_independence_empty_heads() {
    let heads: Vec<Vec<(f64, f64)>> = vec![];
    assert!(verify_head_independence(&heads));
}

#[test]
fn test_head_independence_single_head() {
    let heads = vec![vec![(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]];
    assert!(verify_head_independence(&heads));
}

#[test]
fn test_head_independence_unequal_dims_fails() {
    let heads = vec![
        vec![(0.0, 1.0), (1.0, 2.0)],
        vec![(2.0, 3.0)], // different length
    ];
    assert!(!verify_head_independence(&heads));
}

// ---------------------------------------------------------------------------
// combine_head_outputs
// ---------------------------------------------------------------------------

#[test]
fn test_combine_single_head() {
    let per_head = vec![HeadBounds {
        score_bounds: vec![(0.0, 1.0)],
        output_bounds: vec![(0.5, 0.8), (0.1, 0.3)],
    }];
    let combined = combine_head_outputs(&per_head);
    assert_eq!(combined, vec![(0.5, 0.8), (0.1, 0.3)]);
}

#[test]
fn test_combine_multiple_heads() {
    let per_head = vec![
        HeadBounds {
            score_bounds: vec![(0.0, 1.0)],
            output_bounds: vec![(0.1, 0.2)],
        },
        HeadBounds {
            score_bounds: vec![(0.0, 1.0)],
            output_bounds: vec![(0.3, 0.4)],
        },
        HeadBounds {
            score_bounds: vec![(0.0, 1.0)],
            output_bounds: vec![(0.5, 0.6)],
        },
    ];
    let combined = combine_head_outputs(&per_head);
    assert_eq!(combined.len(), 3);
    assert_eq!(combined[0], (0.1, 0.2));
    assert_eq!(combined[1], (0.3, 0.4));
    assert_eq!(combined[2], (0.5, 0.6));
}

#[test]
fn test_combine_empty_heads() {
    let per_head: Vec<HeadBounds> = vec![];
    let combined = combine_head_outputs(&per_head);
    assert!(combined.is_empty());
}

#[test]
fn test_combine_multi_dim_heads() {
    let per_head = vec![
        HeadBounds {
            score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
            output_bounds: vec![(0.1, 0.2), (0.3, 0.4)],
        },
        HeadBounds {
            score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
            output_bounds: vec![(0.5, 0.6), (0.7, 0.8)],
        },
    ];
    let combined = combine_head_outputs(&per_head);
    assert_eq!(combined.len(), 4);
    assert_eq!(combined[2], (0.5, 0.6));
    assert_eq!(combined[3], (0.7, 0.8));
}

// ---------------------------------------------------------------------------
// verify_multi_head_soundness
// ---------------------------------------------------------------------------

#[test]
fn test_soundness_valid_config() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 2,
        seq_len: 1,
    };
    let input = vec![(0.0, 1.0); 4];
    let hb = HeadBounds {
        score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
    };
    let output = MultiHeadBounds {
        per_head: vec![hb.clone(), hb],
        combined: vec![(0.0, 1.0), (0.0, 1.0), (0.0, 1.0), (0.0, 1.0)],
    };
    assert!(verify_multi_head_soundness(&input, &output, &config));
}

#[test]
fn test_soundness_wrong_num_heads() {
    let config = MultiHeadConfig {
        num_heads: 3,
        head_dim: 2,
        seq_len: 1,
    };
    let input = vec![(0.0, 1.0); 6];
    let hb = HeadBounds {
        score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
    };
    // Only 2 heads but config says 3
    let output = MultiHeadBounds {
        per_head: vec![hb.clone(), hb],
        combined: vec![(0.0, 1.0); 4],
    };
    assert!(!verify_multi_head_soundness(&input, &output, &config));
}

#[test]
fn test_soundness_mismatched_combined() {
    let config = MultiHeadConfig {
        num_heads: 1,
        head_dim: 2,
        seq_len: 1,
    };
    let input = vec![(0.0, 1.0); 2];
    let hb = HeadBounds {
        score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
    };
    // Combined has wrong values
    let output = MultiHeadBounds {
        per_head: vec![hb],
        combined: vec![(999.0, 999.0), (999.0, 999.0)],
    };
    assert!(!verify_multi_head_soundness(&input, &output, &config));
}

#[test]
fn test_soundness_wrong_input_length() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 2,
        seq_len: 1,
    };
    let input = vec![(0.0, 1.0); 3]; // should be 4
    let hb = HeadBounds {
        score_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
        output_bounds: vec![(0.0, 1.0), (0.0, 1.0)],
    };
    let output = MultiHeadBounds {
        per_head: vec![hb.clone(), hb],
        combined: vec![(0.0, 1.0); 4],
    };
    assert!(!verify_multi_head_soundness(&input, &output, &config));
}

// ---------------------------------------------------------------------------
// multi_head_attention_bounds: full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_full_bounds_single_head() {
    let config = MultiHeadConfig {
        num_heads: 1,
        head_dim: 2,
        seq_len: 1,
    };
    let q = vec![(0.0, 1.0), (0.0, 1.0)];
    let k = vec![(0.0, 1.0), (0.0, 1.0)];
    let v = vec![(0.0, 1.0), (0.0, 1.0)];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.per_head.len(), 1);
    assert_eq!(result.combined.len(), 2);
    for &(lo, hi) in &result.combined {
        assert!(lo <= hi + 1e-10, "lo={lo} > hi={hi}");
    }
}

#[test]
fn test_full_bounds_two_heads() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 2,
        seq_len: 1,
    };
    let q = vec![(0.0, 1.0); 4];
    let k = vec![(0.0, 1.0); 4];
    let v = vec![(0.0, 1.0); 4];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.per_head.len(), 2);
    assert_eq!(result.combined.len(), 4);
    // Each head should produce the same bounds (identical inputs)
    assert_eq!(
        result.per_head[0].output_bounds,
        result.per_head[1].output_bounds
    );
}

#[test]
fn test_full_bounds_four_heads() {
    let config = MultiHeadConfig {
        num_heads: 4,
        head_dim: 2,
        seq_len: 1,
    };
    let q = vec![(0.0, 1.0); 8];
    let k = vec![(0.0, 1.0); 8];
    let v = vec![(0.0, 1.0); 8];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.per_head.len(), 4);
    assert_eq!(result.combined.len(), 8);
    // Self-consistency: combined = concat of per_head
    assert!(verify_multi_head_soundness(&q, &result, &config));
}

#[test]
fn test_full_bounds_different_head_inputs() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 1,
        seq_len: 1,
    };
    // Head 0: q=[0,1], k=[0,1], v=[0,1]
    // Head 1: q=[2,3], k=[2,3], v=[2,3]
    let q = vec![(0.0, 1.0), (2.0, 3.0)];
    let k = vec![(0.0, 1.0), (2.0, 3.0)];
    let v = vec![(0.0, 1.0), (2.0, 3.0)];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.per_head.len(), 2);
    // Head 1 has larger values, so output bounds should differ
    let h0_out = &result.per_head[0].output_bounds[0];
    let h1_out = &result.per_head[1].output_bounds[0];
    // Head 1 output should generally be larger (larger v * larger sigmoid)
    assert!(h1_out.1 > h0_out.1 - 1e-6);
}

#[test]
fn test_full_bounds_negative_values() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 2,
        seq_len: 1,
    };
    let q = vec![(-1.0, 0.0); 4];
    let k = vec![(-1.0, 0.0); 4];
    let v = vec![(-2.0, -1.0); 4];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    // v is all negative, so output upper should be <= 0
    for &(_, hi) in &result.combined {
        assert!(hi <= 1e-10, "expected non-positive upper bound, got {hi}");
    }
}

#[test]
fn test_full_bounds_soundness_self_consistency() {
    let config = MultiHeadConfig {
        num_heads: 3,
        head_dim: 2,
        seq_len: 1,
    };
    let q = vec![(0.5, 1.5); 6];
    let k = vec![(0.5, 1.5); 6];
    let v = vec![(1.0, 2.0); 6];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert!(verify_multi_head_soundness(&q, &result, &config));
}

#[test]
fn test_full_bounds_output_intervals_well_formed() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 3,
        seq_len: 1,
    };
    let q: Vec<(f64, f64)> = (0..6)
        .map(|i| (i as f64 * 0.1, i as f64 * 0.1 + 0.5))
        .collect();
    let k = q.clone();
    let v = q.clone();
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    for (i, &(lo, hi)) in result.combined.iter().enumerate() {
        assert!(lo <= hi + 1e-10, "combined[{i}]: lo={lo} > hi={hi}");
    }
    for (h, hb) in result.per_head.iter().enumerate() {
        for (d, &(lo, hi)) in hb.output_bounds.iter().enumerate() {
            assert!(lo <= hi + 1e-10, "head[{h}].output[{d}]: lo={lo} > hi={hi}");
        }
        for (d, &(lo, hi)) in hb.score_bounds.iter().enumerate() {
            assert!(lo <= hi + 1e-10, "head[{h}].score[{d}]: lo={lo} > hi={hi}");
        }
    }
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_single_dim_single_head() {
    let config = MultiHeadConfig {
        num_heads: 1,
        head_dim: 1,
        seq_len: 1,
    };
    let q = vec![(1.0, 1.0)];
    let k = vec![(1.0, 1.0)];
    let v = vec![(1.0, 1.0)];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.combined.len(), 1);
    // sigmoid(1*1/sqrt(1)) = sigmoid(1) ~ 0.731; output ~ 0.731
    let (lo, hi) = result.combined[0];
    let expected = 1.0 / (1.0 + (-1.0f64).exp());
    assert!((lo - expected).abs() < 1e-6);
    assert!((hi - expected).abs() < 1e-6);
}

#[test]
fn test_point_intervals_reduce_to_exact() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 1,
        seq_len: 1,
    };
    // Point intervals (lo == hi)
    let q = vec![(1.0, 1.0), (2.0, 2.0)];
    let k = vec![(1.0, 1.0), (2.0, 2.0)];
    let v = vec![(1.0, 1.0), (1.0, 1.0)];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    // Point intervals should produce narrow output bounds
    for &(lo, hi) in &result.combined {
        assert!(
            (hi - lo).abs() < 1e-6,
            "expected near-point output, got [{lo}, {hi}]"
        );
    }
}

#[test]
fn test_large_num_heads() {
    let config = MultiHeadConfig {
        num_heads: 8,
        head_dim: 1,
        seq_len: 1,
    };
    let q = vec![(0.0, 1.0); 8];
    let k = vec![(0.0, 1.0); 8];
    let v = vec![(0.0, 1.0); 8];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    assert_eq!(result.per_head.len(), 8);
    assert_eq!(result.combined.len(), 8);
    assert!(verify_multi_head_soundness(&q, &result, &config));
}

#[test]
fn test_head_scores_have_correct_dim() {
    let config = MultiHeadConfig {
        num_heads: 2,
        head_dim: 3,
        seq_len: 1,
    };
    let q = vec![(0.0, 1.0); 6];
    let k = vec![(0.0, 1.0); 6];
    let v = vec![(0.0, 1.0); 6];
    let result = multi_head_attention_bounds(&q, &k, &v, &config);
    for hb in &result.per_head {
        assert_eq!(
            hb.score_bounds.len(),
            config.head_dim,
            "score bounds dim should match head_dim"
        );
        assert_eq!(
            hb.output_bounds.len(),
            config.head_dim,
            "output bounds dim should match head_dim"
        );
    }
}

// ---------------------------------------------------------------------------
// Proof spec stubs
// ---------------------------------------------------------------------------

#[test]
fn test_multi_head_specs_derived_pending() {
    let split_spec = MultiHeadSplitSpec::new();
    let combine_spec = MultiHeadCombineSpec::new();
    assert_eq!(split_spec.status(), ProofStatus::DerivedPending);
    assert_eq!(combine_spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_multi_head_specs_default() {
    let split_spec = MultiHeadSplitSpec::default();
    let combine_spec = MultiHeadCombineSpec::default();
    assert_eq!(split_spec.status(), ProofStatus::DerivedPending);
    assert_eq!(combine_spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_multi_head_theorems_count() {
    let theorems = multi_head_theorems();
    assert_eq!(theorems.len(), 2);
    assert_eq!(theorems[0].id, "T55");
    assert_eq!(theorems[1].id, "T56");
}

#[test]
fn test_multi_head_theorems_phase() {
    let theorems = multi_head_theorems();
    for t in &theorems {
        assert_eq!(t.phase, super::Phase::Phase3);
        assert_eq!(t.status, ProofStatus::DerivedPending);
    }
}
