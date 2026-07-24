// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for decision tree optimization and analysis.
//!
//! Part of #3084 - Match expression compilation for native execution.

use super::*;
use crate::match_compile::{compile_match, ConstructorTag, DecisionTree, MatchArm, Pattern, Var};
use crate::native_types::NativeType;
use clean_kernel::Name;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_var(name: &str) -> Var {
    Var {
        name: Name::from_string(name),
        type_: NativeType::UInt64,
    }
}

fn mk_tag(name: &str, arity: usize) -> ConstructorTag {
    ConstructorTag {
        name: Name::from_string(name),
        arity,
    }
}

fn mk_ctor_pat(name: &str, sub: Vec<Pattern>) -> Pattern {
    Pattern::Constructor(Name::from_string(name), sub)
}

fn mk_arm(patterns: Vec<Pattern>, body_idx: usize) -> MatchArm {
    MatchArm {
        patterns,
        guard: None,
        body_idx,
    }
}

fn mk_switch(
    var: &str,
    branches: Vec<(&str, usize, DecisionTree)>,
    default: Option<DecisionTree>,
) -> DecisionTree {
    let v = mk_var(var);
    let bs: Vec<(ConstructorTag, DecisionTree)> = branches
        .into_iter()
        .map(|(name, arity, tree)| (mk_tag(name, arity), tree))
        .collect();
    let d = default.map(Box::new);
    DecisionTree::Switch(v, bs, d)
}

// ---------------------------------------------------------------------------
// TreeStats tests
// ---------------------------------------------------------------------------

#[test]
fn test_stats_single_leaf() {
    let tree = DecisionTree::Leaf(0);
    let s = tree_stats(&tree);
    assert_eq!(s.depth, 0);
    assert_eq!(s.node_count, 1);
    assert_eq!(s.leaf_count, 1);
    assert_eq!(s.switch_count, 0);
    assert_eq!(s.guard_count, 0);
    assert_eq!(s.distinct_bodies, 1);
}

#[test]
fn test_stats_sentinel_leaf() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let s = tree_stats(&tree);
    assert_eq!(s.depth, 0);
    assert_eq!(s.leaf_count, 1);
    // usize::MAX sentinel is not counted as a real body
    assert_eq!(s.distinct_bodies, 0);
}

#[test]
fn test_stats_simple_switch() {
    let tree = mk_switch(
        "x",
        vec![
            ("None", 0, DecisionTree::Leaf(0)),
            ("Some", 1, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let s = tree_stats(&tree);
    assert_eq!(s.depth, 1);
    assert_eq!(s.node_count, 3); // 1 Switch + 2 Leaf
    assert_eq!(s.switch_count, 1);
    assert_eq!(s.leaf_count, 2);
    assert_eq!(s.distinct_bodies, 2);
}

#[test]
fn test_stats_nested_switch() {
    let inner = mk_switch(
        "y",
        vec![
            ("A", 0, DecisionTree::Leaf(10)),
            ("B", 0, DecisionTree::Leaf(20)),
        ],
        None,
    );
    let tree = mk_switch(
        "x",
        vec![("None", 0, DecisionTree::Leaf(0)), ("Some", 1, inner)],
        None,
    );
    let s = tree_stats(&tree);
    assert_eq!(s.depth, 2);
    assert_eq!(s.node_count, 5); // 2 Switch + 3 Leaf
    assert_eq!(s.switch_count, 2);
    assert_eq!(s.leaf_count, 3);
    assert_eq!(s.distinct_bodies, 3);
}

#[test]
fn test_stats_with_guard() {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    let tree = DecisionTree::Guard(
        guard_expr,
        Box::new(DecisionTree::Leaf(0)),
        Box::new(DecisionTree::Leaf(1)),
    );
    let s = tree_stats(&tree);
    assert_eq!(s.depth, 1);
    assert_eq!(s.guard_count, 1);
    assert_eq!(s.node_count, 3);
    assert_eq!(s.distinct_bodies, 2);
}

#[test]
fn test_stats_compiled_option_match() {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    let s = tree_stats(&tree);
    assert!(s.depth >= 1);
    assert!(s.switch_count >= 1);
    assert_eq!(s.distinct_bodies, 2);
}

// ---------------------------------------------------------------------------
// Redundancy detection tests
// ---------------------------------------------------------------------------

#[test]
fn test_detect_redundant_branch_same_as_default() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)), // same as default
        ],
        Some(DecisionTree::Leaf(1)),
    );
    let redundant = detect_redundant_branches(&tree);
    assert_eq!(redundant.len(), 1);
    assert_eq!(redundant[0], ("x".to_string(), "B".to_string()));
}

#[test]
fn test_detect_no_redundancy() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        Some(DecisionTree::Leaf(2)),
    );
    let redundant = detect_redundant_branches(&tree);
    assert!(redundant.is_empty());
}

#[test]
fn test_detect_redundant_nested() {
    let inner = mk_switch(
        "y",
        vec![
            ("C", 0, DecisionTree::Leaf(5)), // same as inner default
        ],
        Some(DecisionTree::Leaf(5)),
    );
    let tree = mk_switch("x", vec![("A", 0, inner)], None);
    let redundant = detect_redundant_branches(&tree);
    assert_eq!(redundant.len(), 1);
    assert_eq!(redundant[0], ("y".to_string(), "C".to_string()));
}

// ---------------------------------------------------------------------------
// Optimization tests
// ---------------------------------------------------------------------------

#[test]
fn test_optimize_hoist_common_leaf() {
    // All branches lead to the same leaf => collapse
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(42)),
            ("B", 0, DecisionTree::Leaf(42)),
        ],
        Some(DecisionTree::Leaf(42)),
    );
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(42));
}

#[test]
fn test_optimize_flatten_single_branch() {
    // Single branch, no default => flatten
    let tree = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(7))], None);
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(7));
}

#[test]
fn test_optimize_prune_default_duplicates() {
    // Branch B is identical to default => pruned
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        Some(DecisionTree::Leaf(1)),
    );
    let opt = optimize_tree(&tree);
    match &opt {
        DecisionTree::Switch(_, branches, default) => {
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, Name::from_string("A"));
            assert!(default.is_some());
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_optimize_guard_same_branches_collapses() {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    let tree = DecisionTree::Guard(
        guard_expr,
        Box::new(DecisionTree::Leaf(3)),
        Box::new(DecisionTree::Leaf(3)),
    );
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(3));
}

#[test]
fn test_optimize_guard_different_branches_preserved() {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    let tree = DecisionTree::Guard(
        guard_expr.clone(),
        Box::new(DecisionTree::Leaf(0)),
        Box::new(DecisionTree::Leaf(1)),
    );
    let opt = optimize_tree(&tree);
    match &opt {
        DecisionTree::Guard(_, s, f) => {
            assert_eq!(s.as_ref(), &DecisionTree::Leaf(0));
            assert_eq!(f.as_ref(), &DecisionTree::Leaf(1));
        }
        other => panic!("expected Guard, got {other:?}"),
    }
}

#[test]
fn test_optimize_nested_hoist() {
    // Outer switch with inner switches that all produce Leaf(0)
    let inner = mk_switch(
        "y",
        vec![
            ("C", 0, DecisionTree::Leaf(0)),
            ("D", 0, DecisionTree::Leaf(0)),
        ],
        Some(DecisionTree::Leaf(0)),
    );
    let tree = mk_switch(
        "x",
        vec![("A", 0, inner), ("B", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(0)),
    );
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(0));
}

#[test]
fn test_optimize_preserves_different_branches() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        Some(DecisionTree::Leaf(2)),
    );
    let opt = optimize_tree(&tree);
    // All branches are different, no optimization possible
    match &opt {
        DecisionTree::Switch(_, branches, default) => {
            assert_eq!(branches.len(), 2);
            assert!(default.is_some());
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_optimize_all_branches_pruned_returns_default() {
    // All branches identical to default => entire switch becomes default
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(9)),
            ("B", 0, DecisionTree::Leaf(9)),
        ],
        Some(DecisionTree::Leaf(9)),
    );
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(9));
}

// ---------------------------------------------------------------------------
// Tree cost tests
// ---------------------------------------------------------------------------

#[test]
fn test_cost_leaf_is_minimal() {
    let c = tree_cost(&DecisionTree::Leaf(0));
    assert_eq!(c, 1);
}

#[test]
fn test_cost_deeper_tree_costs_more() {
    let shallow = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let deep = mk_switch(
        "x",
        vec![(
            "A",
            0,
            mk_switch("y", vec![("B", 0, DecisionTree::Leaf(0))], None),
        )],
        None,
    );
    assert!(tree_cost(&deep) > tree_cost(&shallow));
}

// ---------------------------------------------------------------------------
// Utility function tests
// ---------------------------------------------------------------------------

#[test]
fn test_replace_fail_sentinel() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(usize::MAX)),
    );
    let replaced = replace_fail_sentinel(&tree, 99);
    match &replaced {
        DecisionTree::Switch(_, _, Some(def)) => {
            assert_eq!(def.as_ref(), &DecisionTree::Leaf(99));
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_replace_fail_sentinel_preserves_normal_leaves() {
    let tree = DecisionTree::Leaf(5);
    let replaced = replace_fail_sentinel(&tree, 99);
    assert_eq!(replaced, DecisionTree::Leaf(5));
}

#[test]
fn test_reachable_bodies_simple() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        Some(DecisionTree::Leaf(2)),
    );
    let bodies = reachable_bodies(&tree);
    let expected: HashSet<usize> = [0, 1, 2].into_iter().collect();
    assert_eq!(bodies, expected);
}

#[test]
fn test_reachable_bodies_includes_sentinel() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(usize::MAX)),
    );
    let bodies = reachable_bodies(&tree);
    assert!(bodies.contains(&0));
    assert!(bodies.contains(&usize::MAX));
}

#[test]
fn test_count_fail_sentinels_none() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    assert_eq!(count_fail_sentinels(&tree), 0);
}

#[test]
fn test_count_fail_sentinels_some() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(usize::MAX)),
    );
    assert_eq!(count_fail_sentinels(&tree), 1);
}

// ---------------------------------------------------------------------------
// Validation tests
// ---------------------------------------------------------------------------

#[test]
fn test_validate_well_formed_tree() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let errors = validate_tree(&tree);
    assert!(errors.is_empty());
}

#[test]
fn test_validate_empty_switch_no_default() {
    let tree = DecisionTree::Switch(mk_var("x"), vec![], None);
    let errors = validate_tree(&tree);
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("no branches and no default"));
}

#[test]
fn test_validate_duplicate_tags() {
    let tree = DecisionTree::Switch(
        mk_var("x"),
        vec![
            (mk_tag("A", 0), DecisionTree::Leaf(0)),
            (mk_tag("A", 0), DecisionTree::Leaf(1)),
        ],
        None,
    );
    let errors = validate_tree(&tree);
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("duplicate tag A"));
}

// ---------------------------------------------------------------------------
// map_body_indices tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_body_indices_leaf() {
    let tree = DecisionTree::Leaf(3);
    let mapped = map_body_indices(&tree, &|idx| idx + 10);
    assert_eq!(mapped, DecisionTree::Leaf(13));
}

#[test]
fn test_map_body_indices_switch() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        Some(DecisionTree::Leaf(2)),
    );
    let mapped = map_body_indices(&tree, &|idx| idx * 2);
    match &mapped {
        DecisionTree::Switch(_, branches, Some(def)) => {
            assert_eq!(branches[0].1, DecisionTree::Leaf(0));
            assert_eq!(branches[1].1, DecisionTree::Leaf(2));
            assert_eq!(def.as_ref(), &DecisionTree::Leaf(4));
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Integration: compile then optimize
// ---------------------------------------------------------------------------

#[test]
fn test_optimize_compiled_wildcard_only() {
    // match x with _ => 0 produces Leaf(0), optimization is no-op
    let scrutinees = vec![mk_var("x")];
    let arms = vec![mk_arm(vec![Pattern::Wildcard], 0)];
    let tree = compile_match(&scrutinees, &arms);
    let opt = optimize_tree(&tree);
    assert_eq!(opt, DecisionTree::Leaf(0));
}

#[test]
fn test_optimize_compiled_option_match() {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    let opt = optimize_tree(&tree);
    // Optimization should not change semantics. Both branches are different,
    // so the structure should be similar.
    let orig_stats = tree_stats(&tree);
    let opt_stats = tree_stats(&opt);
    assert!(opt_stats.node_count <= orig_stats.node_count);
    assert!(opt_stats.depth <= orig_stats.depth);
}

#[test]
fn test_optimize_compiled_redundant_default() {
    // match x with
    // | A => 0
    // | B => 1
    // | _ => 1   <- same as B, B becomes redundant relative to default
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 1),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    let opt = optimize_tree(&tree);
    // B branch should be pruned since it matches default
    let opt_stats = tree_stats(&opt);
    let orig_stats = tree_stats(&tree);
    assert!(opt_stats.node_count <= orig_stats.node_count);
}
