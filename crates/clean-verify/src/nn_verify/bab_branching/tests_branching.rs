// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BaB branching heuristics and proof complexity lower bounds.

use super::branching::*;
use super::tree::NeuronId;
use crate::nn_verify::ibp_crown::Interval;

// ---------------------------------------------------------------------------
// proof_complexity_lower_bound tests
// ---------------------------------------------------------------------------

#[test]
fn test_complexity_trivial_zero_unfixed() {
    let bound = proof_complexity_lower_bound(&[]);
    assert!((bound - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_complexity_trivial_one_unfixed() {
    let bounds = [Interval::new(-1.0, 1.0)];
    let bound = proof_complexity_lower_bound(&bounds);
    assert!((bound - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_complexity_increases_with_unfixed_count() {
    let small: Vec<Interval> = (0..4).map(|_| Interval::new(-1.0, 1.0)).collect();
    let large: Vec<Interval> = (0..16).map(|_| Interval::new(-1.0, 1.0)).collect();

    let c_small = proof_complexity_lower_bound(&small);
    let c_large = proof_complexity_lower_bound(&large);

    assert!(
        c_large > c_small,
        "more unfixed neurons should yield higher complexity: {} vs {}",
        c_large,
        c_small
    );
}

#[test]
fn test_complexity_centered_harder_than_skewed() {
    // Centered bounds (zero in the middle) should be harder than skewed.
    let centered: Vec<Interval> = (0..8).map(|_| Interval::new(-1.0, 1.0)).collect();
    let skewed: Vec<Interval> = (0..8).map(|_| Interval::new(-0.1, 2.0)).collect();

    let c_centered = proof_complexity_lower_bound(&centered);
    let c_skewed = proof_complexity_lower_bound(&skewed);

    assert!(
        c_centered > c_skewed,
        "centered intervals should yield higher complexity: {} vs {}",
        c_centered,
        c_skewed
    );
}

// ---------------------------------------------------------------------------
// score_candidate tests
// ---------------------------------------------------------------------------

#[test]
fn test_score_proof_complexity_balanced() {
    let candidates = [
        BranchCandidate {
            neuron: NeuronId::new(0, 0),
            bounds: Interval::new(-1.0, 1.0), // Centered: good split.
        },
        BranchCandidate {
            neuron: NeuronId::new(0, 1),
            bounds: Interval::new(-0.1, 5.0), // Skewed: poor split.
        },
    ];

    let all_bounds: Vec<Interval> = candidates.iter().map(|c| c.bounds).collect();

    let score0 = score_candidate(
        &candidates[0],
        0,
        &all_bounds,
        BranchingHeuristic::ProofComplexityBalanced,
    );
    let score1 = score_candidate(
        &candidates[1],
        1,
        &all_bounds,
        BranchingHeuristic::ProofComplexityBalanced,
    );

    // Both scores should be non-negative.
    assert!(score0.score >= 0.0);
    assert!(score1.score >= 0.0);

    // Complexity estimates should be positive.
    assert!(score0.complexity_active > 0.0);
    assert!(score0.complexity_inactive > 0.0);
}

#[test]
fn test_score_max_interval() {
    let wide = BranchCandidate {
        neuron: NeuronId::new(0, 0),
        bounds: Interval::new(-5.0, 5.0),
    };
    let narrow = BranchCandidate {
        neuron: NeuronId::new(0, 1),
        bounds: Interval::new(-0.5, 0.5),
    };

    let all_bounds = vec![wide.bounds, narrow.bounds];

    let s_wide = score_candidate(&wide, 0, &all_bounds, BranchingHeuristic::MaxInterval);
    let s_narrow = score_candidate(&narrow, 1, &all_bounds, BranchingHeuristic::MaxInterval);

    assert!(
        s_wide.score > s_narrow.score,
        "wider interval should score higher: {} vs {}",
        s_wide.score,
        s_narrow.score
    );
}

#[test]
fn test_score_most_ambiguous() {
    let centered = BranchCandidate {
        neuron: NeuronId::new(0, 0),
        bounds: Interval::new(-2.0, 2.0), // Perfectly centered: ambiguity = 1.0.
    };
    let skewed = BranchCandidate {
        neuron: NeuronId::new(0, 1),
        bounds: Interval::new(-0.1, 3.0), // Skewed: lower ambiguity.
    };

    let all_bounds = vec![centered.bounds, skewed.bounds];

    let s_centered = score_candidate(&centered, 0, &all_bounds, BranchingHeuristic::MostAmbiguous);
    let s_skewed = score_candidate(&skewed, 1, &all_bounds, BranchingHeuristic::MostAmbiguous);

    assert!(
        s_centered.score > s_skewed.score,
        "centered interval should be more ambiguous: {} vs {}",
        s_centered.score,
        s_skewed.score
    );
}

// ---------------------------------------------------------------------------
// select_best_branch tests
// ---------------------------------------------------------------------------

#[test]
fn test_select_best_branch_empty() {
    assert!(select_best_branch(&[], BranchingHeuristic::ProofComplexityBalanced).is_none());
}

#[test]
fn test_select_best_branch_single_candidate() {
    let candidates = vec![BranchCandidate {
        neuron: NeuronId::new(0, 0),
        bounds: Interval::new(-1.0, 1.0),
    }];

    let result = select_best_branch(&candidates, BranchingHeuristic::ProofComplexityBalanced);
    assert!(result.is_some());
    assert_eq!(result.expect("should select").neuron, NeuronId::new(0, 0));
}

#[test]
fn test_select_best_branch_max_interval_picks_widest() {
    let candidates = vec![
        BranchCandidate {
            neuron: NeuronId::new(0, 0),
            bounds: Interval::new(-1.0, 1.0),
        },
        BranchCandidate {
            neuron: NeuronId::new(0, 1),
            bounds: Interval::new(-5.0, 5.0),
        },
        BranchCandidate {
            neuron: NeuronId::new(0, 2),
            bounds: Interval::new(-0.5, 0.5),
        },
    ];

    let result =
        select_best_branch(&candidates, BranchingHeuristic::MaxInterval).expect("should select");
    assert_eq!(result.neuron, NeuronId::new(0, 1));
}

// ---------------------------------------------------------------------------
// verify_balanced_split_optimality tests
// ---------------------------------------------------------------------------

#[test]
fn test_balanced_split_optimality_trivial() {
    // Empty and single candidates are vacuously optimal.
    assert!(verify_balanced_split_optimality(&[]));
    assert!(verify_balanced_split_optimality(&[BranchCandidate {
        neuron: NeuronId::new(0, 0),
        bounds: Interval::new(-1.0, 1.0),
    }]));
}

#[test]
fn test_balanced_split_optimality_multiple_candidates() {
    let candidates: Vec<BranchCandidate> = (0..6)
        .map(|i| BranchCandidate {
            neuron: NeuronId::new(0, i),
            bounds: Interval::new(-(i as f64 + 1.0), i as f64 + 1.0),
        })
        .collect();

    // The optimality check should confirm that the selected candidate
    // has the highest min-complexity score.
    assert!(verify_balanced_split_optimality(&candidates));
}

// ---------------------------------------------------------------------------
// verify_complexity_monotonicity tests
// ---------------------------------------------------------------------------

#[test]
fn test_complexity_monotonicity_trivial() {
    assert!(verify_complexity_monotonicity(&[]));
    assert!(verify_complexity_monotonicity(&[Interval::new(-1.0, 1.0)]));
}

#[test]
fn test_complexity_monotonicity_centered_intervals() {
    let bounds: Vec<Interval> = (0..8).map(|_| Interval::new(-1.0, 1.0)).collect();
    assert!(
        verify_complexity_monotonicity(&bounds),
        "monotonicity should hold for centered intervals"
    );
}

#[test]
fn test_complexity_monotonicity_mixed_intervals() {
    let bounds = vec![
        Interval::new(-2.0, 1.0),
        Interval::new(-0.5, 3.0),
        Interval::new(-1.0, 1.0),
        Interval::new(-3.0, 0.5),
    ];
    assert!(
        verify_complexity_monotonicity(&bounds),
        "monotonicity should hold for mixed intervals"
    );
}

// ---------------------------------------------------------------------------
// tree_size_bound tests
// ---------------------------------------------------------------------------

#[test]
fn test_tree_size_bound_trivial() {
    assert!((tree_size_bound(1.0) - 1.0).abs() < f64::EPSILON);
    assert!((tree_size_bound(0.5) - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_tree_size_bound_monotone() {
    let b2 = tree_size_bound(2.0);
    let b4 = tree_size_bound(4.0);
    let b8 = tree_size_bound(8.0);

    assert!(b4 > b2, "bound should be monotone: {} vs {}", b4, b2);
    assert!(b8 > b4, "bound should be monotone: {} vs {}", b8, b4);
}

#[test]
fn test_tree_size_bound_values() {
    // tree_size_bound(4.0) = 4.0 * log2(4.0) = 4.0 * 2.0 = 8.0
    let b = tree_size_bound(4.0);
    assert!((b - 8.0).abs() < f64::EPSILON, "expected 8.0, got {}", b);
}

// ---------------------------------------------------------------------------
// Integration: branching + tree construction
// ---------------------------------------------------------------------------

#[test]
fn test_bab_workflow_small_network() {
    use super::tree::{BabTree, VerificationResult};

    // Simulate a 3-neuron unfixed network.
    let candidates = vec![
        BranchCandidate {
            neuron: NeuronId::new(0, 0),
            bounds: Interval::new(-1.0, 1.0),
        },
        BranchCandidate {
            neuron: NeuronId::new(0, 1),
            bounds: Interval::new(-2.0, 2.0),
        },
        BranchCandidate {
            neuron: NeuronId::new(0, 2),
            bounds: Interval::new(-0.5, 0.5),
        },
    ];

    // Select best branch.
    let best = select_best_branch(&candidates, BranchingHeuristic::ProofComplexityBalanced)
        .expect("should select a candidate");

    // Build a BaB tree with this split.
    let mut tree = BabTree::new();
    let (active, inactive) = tree
        .split_node(tree.root(), best.neuron)
        .expect("split should succeed");

    // Verify both branches.
    tree.set_result(active, VerificationResult::Safe);
    tree.set_result(inactive, VerificationResult::Safe);

    assert_eq!(tree.overall_result(), Some(VerificationResult::Safe));
    assert_eq!(tree.size(), 3);
    assert!(tree.is_complete());
}
