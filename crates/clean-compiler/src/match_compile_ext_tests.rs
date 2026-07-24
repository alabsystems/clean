// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended match compilation analysis.
//!
//! Part of #3084 - Match expression compilation for native execution.

use super::match_compile_ext::*;
use crate::match_compile::{compile_match, ConstructorTag, DecisionTree, MatchArm, Pattern, Var};
use crate::native_types::NativeType;
use clean_kernel::expr::Literal;
use clean_kernel::Name;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_var(name: &str) -> Var {
    Var {
        name: Name::from_string(name),
        type_: NativeType::UInt64,
    }
}

fn mk_ctor_pat(name: &str, sub: Vec<Pattern>) -> Pattern {
    Pattern::Constructor(Name::from_string(name), sub)
}

fn mk_var_pat(name: &str) -> Pattern {
    Pattern::Variable(Name::from_string(name))
}

fn mk_arm(patterns: Vec<Pattern>, body_idx: usize) -> MatchArm {
    MatchArm {
        patterns,
        guard: None,
        body_idx,
    }
}

fn mk_guarded_arm(patterns: Vec<Pattern>, body_idx: usize) -> MatchArm {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    MatchArm {
        patterns,
        guard: Some(guard_expr),
        body_idx,
    }
}

// ===========================================================================
// Arm scoring tests
// ===========================================================================

#[test]
fn test_score_arm_wildcard_only() {
    let arm = mk_arm(vec![Pattern::Wildcard], 0);
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 0);
    assert_eq!(score.wildcard_count, 1);
    assert_eq!(score.total_arity, 0);
}

#[test]
fn test_score_arm_single_constructor_no_fields() {
    let arm = mk_arm(vec![mk_ctor_pat("None", vec![])], 0);
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 1);
    assert_eq!(score.wildcard_count, 0);
    assert_eq!(score.total_arity, 0);
}

#[test]
fn test_score_arm_constructor_with_fields() {
    let arm = mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 0);
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 1);
    assert_eq!(score.total_arity, 1);
    assert_eq!(score.wildcard_count, 1);
}

#[test]
fn test_score_arm_nested_constructors() {
    let arm = mk_arm(
        vec![mk_ctor_pat(
            "Some",
            vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])],
        )],
        0,
    );
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 2);
    assert_eq!(score.max_depth, 3);
}

#[test]
fn test_score_arm_variable_pattern() {
    let arm = mk_arm(vec![mk_var_pat("x")], 0);
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 0);
    assert_eq!(score.wildcard_count, 1);
}

#[test]
fn test_score_arm_literal_pattern() {
    let arm = mk_arm(vec![Pattern::Literal(Literal::Nat(42u64.into()))], 0);
    let score = score_arm(&arm);
    assert_eq!(score.specificity, 1);
    assert_eq!(score.wildcard_count, 0);
}

#[test]
fn test_score_arm_or_pattern() {
    let arm = mk_arm(
        vec![Pattern::Or(vec![
            mk_ctor_pat("A", vec![]),
            mk_ctor_pat("B", vec![]),
        ])],
        0,
    );
    let score = score_arm(&arm);
    assert!(score.specificity >= 1);
}

#[test]
fn test_score_arms_returns_correct_count() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let scores = score_arms(&arms);
    assert_eq!(scores.len(), 2);
}

#[test]
fn test_rank_arms_by_specificity_most_specific_first() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(
            vec![mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])])],
            1,
        ),
        mk_arm(vec![mk_ctor_pat("None", vec![])], 2),
    ];
    let ranking = rank_arms_by_specificity(&arms);
    // Arm 1 (specificity 2) > Arm 2 (specificity 1) > Arm 0 (specificity 0)
    assert_eq!(ranking[0], 1);
    assert_eq!(ranking[1], 2);
    assert_eq!(ranking[2], 0);
}

#[test]
fn test_rank_arms_tiebreak_by_fewer_wildcards() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![]), mk_ctor_pat("B", vec![])], 1),
    ];
    let ranking = rank_arms_by_specificity(&arms);
    // Arm 1 has specificity 2, Arm 0 has specificity 1
    assert_eq!(ranking[0], 1);
}

// ===========================================================================
// Column selection strategy tests
// ===========================================================================

#[test]
fn test_first_column_strategy_always_picks_zero() {
    let arms = vec![mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("A", vec![])], 0)];
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let col = pick_column_with_strategy(&scrutinees, &arms, ColumnStrategy::FirstColumn)
        .expect("should succeed");
    assert_eq!(col, 0);
}

#[test]
fn test_most_constructors_strategy() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("B", vec![])], 1),
    ];
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let col = pick_column_with_strategy(&scrutinees, &arms, ColumnStrategy::MostConstructors)
        .expect("should succeed");
    assert_eq!(col, 1, "column 1 has 2 constructors, column 0 has 0");
}

#[test]
fn test_fewest_wildcards_strategy() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![]), Pattern::Wildcard], 1),
    ];
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let col = pick_column_with_strategy(&scrutinees, &arms, ColumnStrategy::FewestWildcards)
        .expect("should succeed");
    assert_eq!(col, 0, "column 0 has 0 wildcards, column 1 has 2");
}

#[test]
fn test_smallest_branching_factor_strategy() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), mk_ctor_pat("X", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![]), mk_ctor_pat("X", vec![])], 1),
        mk_arm(vec![mk_ctor_pat("C", vec![]), mk_ctor_pat("Y", vec![])], 2),
    ];
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let col =
        pick_column_with_strategy(&scrutinees, &arms, ColumnStrategy::SmallestBranchingFactor)
            .expect("should succeed");
    assert_eq!(col, 1, "column 1 has 2 distinct ctors, column 0 has 3");
}

#[test]
fn test_pick_column_empty_scrutinees_returns_error() {
    let arms = vec![mk_arm(vec![], 0)];
    let result = pick_column_with_strategy(&[], &arms, ColumnStrategy::FirstColumn);
    assert!(result.is_err());
}

// ===========================================================================
// Overlap detection tests
// ===========================================================================

#[test]
fn test_no_overlaps_disjoint_constructors() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert!(overlaps.is_empty());
}

#[test]
fn test_overlap_wildcard_with_constructor() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert_eq!(overlaps.len(), 1);
    assert_eq!(overlaps[0].arm_a, 0);
    assert_eq!(overlaps[0].arm_b, 1);
}

#[test]
fn test_overlap_same_constructor() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert_eq!(overlaps.len(), 1);
}

#[test]
fn test_overlap_nested_constructors() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 0),
        mk_arm(
            vec![mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])])],
            1,
        ),
    ];
    let overlaps = detect_overlaps(&arms);
    assert_eq!(overlaps.len(), 1, "wildcard sub-pat overlaps None sub-pat");
}

#[test]
fn test_no_overlap_different_constructors_nested() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("Some", vec![mk_ctor_pat("A", vec![])])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![mk_ctor_pat("B", vec![])])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert!(overlaps.is_empty(), "A and B are disjoint");
}

#[test]
fn test_overlap_multi_column() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![]), mk_ctor_pat("B", vec![])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert_eq!(overlaps.len(), 1);
    assert_eq!(overlaps[0].overlapping_columns.len(), 2);
}

#[test]
fn test_no_overlap_disjoint_multi_column() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), mk_ctor_pat("X", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![]), mk_ctor_pat("Y", vec![])], 1),
    ];
    let overlaps = detect_overlaps(&arms);
    assert!(overlaps.is_empty());
}

#[test]
fn test_overlap_or_pattern() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(
            vec![Pattern::Or(vec![
                mk_ctor_pat("A", vec![]),
                mk_ctor_pat("B", vec![]),
            ])],
            1,
        ),
    ];
    let overlaps = detect_overlaps(&arms);
    assert_eq!(overlaps.len(), 1, "or-pattern containing A overlaps A");
}

// ===========================================================================
// Shadow detection tests
// ===========================================================================

#[test]
fn test_is_arm_shadowed_by_wildcard() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    assert!(is_arm_shadowed(&arms, 1));
}

#[test]
fn test_first_arm_never_shadowed() {
    let arms = vec![mk_arm(vec![Pattern::Wildcard], 0)];
    assert!(!is_arm_shadowed(&arms, 0));
}

#[test]
fn test_not_shadowed_disjoint() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
    ];
    assert!(!is_arm_shadowed(&arms, 1));
}

#[test]
fn test_shadowed_by_same_constructor() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    assert!(is_arm_shadowed(&arms, 1));
}

#[test]
fn test_guarded_arm_does_not_shadow() {
    let arms = vec![
        mk_guarded_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    assert!(
        !is_arm_shadowed(&arms, 1),
        "guarded arm cannot fully shadow"
    );
}

// ===========================================================================
// Patterns overlap unit tests
// ===========================================================================

#[test]
fn test_patterns_overlap_wildcard_anything() {
    assert!(patterns_overlap(
        &Pattern::Wildcard,
        &mk_ctor_pat("A", vec![])
    ));
    assert!(patterns_overlap(
        &mk_ctor_pat("A", vec![]),
        &Pattern::Wildcard
    ));
}

#[test]
fn test_patterns_overlap_same_literal() {
    let a = Pattern::Literal(Literal::Nat(42u64.into()));
    let b = Pattern::Literal(Literal::Nat(42u64.into()));
    assert!(patterns_overlap(&a, &b));
}

#[test]
fn test_patterns_no_overlap_different_literals() {
    let a = Pattern::Literal(Literal::Nat(1u64.into()));
    let b = Pattern::Literal(Literal::Nat(2u64.into()));
    assert!(!patterns_overlap(&a, &b));
}

#[test]
fn test_patterns_no_overlap_constructor_literal() {
    let a = mk_ctor_pat("A", vec![]);
    let b = Pattern::Literal(Literal::Nat(1u64.into()));
    assert!(!patterns_overlap(&a, &b));
}

// ===========================================================================
// Exhaustiveness gap reporting tests
// ===========================================================================

#[test]
fn test_exhaustiveness_no_gaps_wildcard() {
    let arms = vec![mk_arm(vec![Pattern::Wildcard], 0)];
    let mut known = HashMap::new();
    known.insert(0, vec!["A".to_string(), "B".to_string()]);
    let gaps = report_exhaustiveness_gaps(&arms, &known);
    assert!(gaps.is_empty(), "wildcard covers everything");
}

#[test]
fn test_exhaustiveness_missing_constructor() {
    let arms = vec![mk_arm(vec![mk_ctor_pat("A", vec![])], 0)];
    let mut known = HashMap::new();
    known.insert(0, vec!["A".to_string(), "B".to_string()]);
    let gaps = report_exhaustiveness_gaps(&arms, &known);
    assert_eq!(gaps.len(), 1);
    assert!(gaps[0].description.contains("B"));
    assert_eq!(gaps[0].column, 0);
}

#[test]
fn test_exhaustiveness_multiple_gaps() {
    let arms = vec![mk_arm(vec![mk_ctor_pat("A", vec![])], 0)];
    let mut known = HashMap::new();
    known.insert(0, vec!["A".to_string(), "B".to_string(), "C".to_string()]);
    let gaps = report_exhaustiveness_gaps(&arms, &known);
    assert_eq!(gaps.len(), 2);
}

#[test]
fn test_exhaustiveness_no_gaps_all_covered() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
    ];
    let mut known = HashMap::new();
    known.insert(0, vec!["A".to_string(), "B".to_string()]);
    let gaps = report_exhaustiveness_gaps(&arms, &known);
    assert!(gaps.is_empty());
}

// ===========================================================================
// Match statistics tests
// ===========================================================================

#[test]
fn test_match_stats_empty() {
    let stats = compute_match_stats(&[], 0);
    assert_eq!(stats.arm_count, 0);
    assert_eq!(stats.total_pattern_nodes, 0);
    assert!((stats.wildcard_ratio - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_match_stats_single_wildcard() {
    let arms = vec![mk_arm(vec![Pattern::Wildcard], 0)];
    let stats = compute_match_stats(&arms, 1);
    assert_eq!(stats.arm_count, 1);
    assert_eq!(stats.column_count, 1);
    assert_eq!(stats.total_pattern_nodes, 1);
    assert!((stats.wildcard_ratio - 1.0).abs() < f64::EPSILON);
    assert_eq!(stats.constructor_count, 0);
}

#[test]
fn test_match_stats_mixed_patterns() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![Pattern::Wildcard])], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let stats = compute_match_stats(&arms, 1);
    assert_eq!(stats.arm_count, 2);
    // Arm 0: Ctor("A", [Wildcard]) = 2 nodes (1 ctor + 1 wild), Arm 1: Wildcard = 1 node
    assert_eq!(stats.total_pattern_nodes, 3);
    assert_eq!(stats.constructor_count, 1);
    assert!((stats.wildcard_ratio - 2.0 / 3.0).abs() < 0.01);
}

#[test]
fn test_match_stats_or_pattern_count() {
    let arms = vec![mk_arm(
        vec![Pattern::Or(vec![
            mk_ctor_pat("A", vec![]),
            mk_ctor_pat("B", vec![]),
        ])],
        0,
    )];
    let stats = compute_match_stats(&arms, 1);
    assert_eq!(stats.or_pattern_count, 1);
}

#[test]
fn test_match_stats_literal_count() {
    let arms = vec![mk_arm(vec![Pattern::Literal(Literal::Nat(5u64.into()))], 0)];
    let stats = compute_match_stats(&arms, 1);
    assert_eq!(stats.literal_count, 1);
    assert_eq!(stats.constructor_count, 0);
}

#[test]
fn test_match_stats_nesting_depth() {
    let arm = mk_arm(
        vec![mk_ctor_pat(
            "Some",
            vec![mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])])],
        )],
        0,
    );
    let stats = compute_match_stats(&[arm], 1);
    assert_eq!(stats.max_nesting_depth, 3);
}

// ===========================================================================
// Decision tree metrics tests
// ===========================================================================

#[test]
fn test_tree_metrics_single_leaf() {
    let tree = DecisionTree::Leaf(0);
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.height, 0);
    assert_eq!(metrics.total_nodes, 1);
    assert_eq!(metrics.leaf_count, 1);
    assert_eq!(metrics.switch_count, 0);
    assert_eq!(metrics.unreachable_leaves, 0);
}

#[test]
fn test_tree_metrics_sentinel_leaf() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.unreachable_leaves, 1);
}

#[test]
fn test_tree_metrics_simple_switch() {
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![
            (
                ConstructorTag {
                    name: Name::from_string("A"),
                    arity: 0,
                },
                DecisionTree::Leaf(0),
            ),
            (
                ConstructorTag {
                    name: Name::from_string("B"),
                    arity: 0,
                },
                DecisionTree::Leaf(1),
            ),
        ],
        None,
    );
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.height, 1);
    assert_eq!(metrics.total_nodes, 3);
    assert_eq!(metrics.switch_count, 1);
    assert_eq!(metrics.leaf_count, 2);
    assert!((metrics.avg_path_length - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_tree_metrics_duplicate_leaves() {
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![
            (
                ConstructorTag {
                    name: Name::from_string("A"),
                    arity: 0,
                },
                DecisionTree::Leaf(0),
            ),
            (
                ConstructorTag {
                    name: Name::from_string("B"),
                    arity: 0,
                },
                DecisionTree::Leaf(0),
            ),
        ],
        None,
    );
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.duplicate_leaves, 1, "body 0 appears twice");
}

#[test]
fn test_tree_metrics_with_default() {
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![(
            ConstructorTag {
                name: Name::from_string("A"),
                arity: 0,
            },
            DecisionTree::Leaf(0),
        )],
        Some(Box::new(DecisionTree::Leaf(1))),
    );
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.total_nodes, 3);
    assert_eq!(metrics.leaf_count, 2);
}

#[test]
fn test_tree_metrics_compiled_option_match() {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    let metrics = compute_tree_metrics(&tree);
    assert!(metrics.height >= 1);
    assert!(metrics.switch_count >= 1);
    assert_eq!(metrics.unreachable_leaves, 0);
}

#[test]
fn test_tree_metrics_guard_node() {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    let tree = DecisionTree::Guard(
        guard_expr,
        Box::new(DecisionTree::Leaf(0)),
        Box::new(DecisionTree::Leaf(1)),
    );
    let metrics = compute_tree_metrics(&tree);
    assert_eq!(metrics.guard_count, 1);
    assert_eq!(metrics.leaf_count, 2);
    assert_eq!(metrics.total_nodes, 3);
}

// ===========================================================================
// Pattern complexity tests
// ===========================================================================

#[test]
fn test_pattern_complexity_wildcard() {
    assert_eq!(pattern_complexity(&Pattern::Wildcard), 0);
}

#[test]
fn test_pattern_complexity_literal() {
    assert_eq!(
        pattern_complexity(&Pattern::Literal(Literal::Nat(1u64.into()))),
        1
    );
}

#[test]
fn test_pattern_complexity_constructor_no_fields() {
    assert_eq!(pattern_complexity(&mk_ctor_pat("A", vec![])), 2);
}

#[test]
fn test_pattern_complexity_constructor_with_wild_field() {
    assert_eq!(
        pattern_complexity(&mk_ctor_pat("Some", vec![Pattern::Wildcard])),
        2
    );
}

#[test]
fn test_pattern_complexity_nested() {
    let pat = mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])]);
    // Some(None) = 2 + (2 + 0) = 4
    assert_eq!(pattern_complexity(&pat), 4);
}

#[test]
fn test_match_complexity_sums_all_arms() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    // A = 2, Wildcard = 0, total = 2
    assert_eq!(match_complexity(&arms), 2);
}

// ===========================================================================
// Distinct constructors per column tests
// ===========================================================================

#[test]
fn test_distinct_constructors_single_column() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 2),
    ];
    let counts = distinct_constructors_per_column(&arms, 1);
    assert_eq!(counts, vec![2], "A and B are distinct");
}

#[test]
fn test_distinct_constructors_two_columns() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), mk_ctor_pat("X", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![]), mk_ctor_pat("X", vec![])], 1),
    ];
    let counts = distinct_constructors_per_column(&arms, 2);
    assert_eq!(counts, vec![2, 1]);
}

#[test]
fn test_distinct_constructors_wildcards_not_counted() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    let counts = distinct_constructors_per_column(&arms, 1);
    assert_eq!(counts, vec![1]);
}

// ===========================================================================
// Wildcards per column tests
// ===========================================================================

#[test]
fn test_wildcards_per_column_all_wild() {
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let counts = wildcards_per_column(&arms, 1);
    assert_eq!(counts, vec![2]);
}

#[test]
fn test_wildcards_per_column_no_wilds() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
    ];
    let counts = wildcards_per_column(&arms, 1);
    assert_eq!(counts, vec![0]);
}

#[test]
fn test_wildcards_per_column_mixed() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), Pattern::Wildcard], 0),
        mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("B", vec![])], 1),
    ];
    let counts = wildcards_per_column(&arms, 2);
    assert_eq!(counts, vec![1, 1]);
}

#[test]
fn test_wildcards_per_column_variable_counts_as_wild() {
    let arms = vec![mk_arm(vec![mk_var_pat("x")], 0)];
    let counts = wildcards_per_column(&arms, 1);
    assert_eq!(counts, vec![1]);
}
