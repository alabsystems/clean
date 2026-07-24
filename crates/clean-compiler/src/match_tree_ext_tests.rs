// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended decision tree analysis (match_tree_ext).
//!
//! Part of #3084 - Match expression compilation for native execution.

use crate::match_compile::{ConstructorTag, DecisionTree, Var};
use crate::match_tree_ext::*;
use crate::native_types::NativeType;
use clean_kernel::Name;

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

fn mk_guard(success: DecisionTree, failure: DecisionTree) -> DecisionTree {
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    DecisionTree::Guard(guard_expr, Box::new(success), Box::new(failure))
}

// ---------------------------------------------------------------------------
// Sharing detection tests
// ---------------------------------------------------------------------------

#[test]
fn test_sharing_stats_single_leaf() {
    let tree = DecisionTree::Leaf(0);
    let s = sharing_stats(&tree);
    assert_eq!(s.total_nodes, 1);
    assert_eq!(s.unique_nodes, 1);
    assert_eq!(s.shared_nodes, 0);
    assert!((s.sharing_ratio - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_sharing_stats_identical_leaves() {
    // Two branches leading to the same Leaf(0) => sharing detected
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(0)),
        ],
        None,
    );
    let s = sharing_stats(&tree);
    // Total: 1 switch + 2 leaves = 3 nodes
    assert_eq!(s.total_nodes, 3);
    // Leaf(0) appears twice with same hash => shared_nodes > 0
    assert!(s.shared_nodes > 0);
}

#[test]
fn test_sharing_stats_distinct_leaves() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let s = sharing_stats(&tree);
    assert_eq!(s.total_nodes, 3);
    // All different => unique_nodes == total_nodes
    assert_eq!(s.unique_nodes, 3);
    assert_eq!(s.shared_nodes, 0);
}

#[test]
fn test_hash_subtree_path_tracking() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(5)),
            ("B", 0, DecisionTree::Leaf(5)),
            ("C", 0, DecisionTree::Leaf(5)),
        ],
        None,
    );
    let hashes = hash_subtree(&tree);
    // Leaf(5) hash should have 3 paths
    let leaf_paths: Vec<_> = hashes.values().filter(|paths| paths.len() == 3).collect();
    assert_eq!(leaf_paths.len(), 1);
}

#[test]
fn test_sharing_stats_nested_sharing() {
    let inner = mk_switch("y", vec![("C", 0, DecisionTree::Leaf(1))], None);
    let tree = mk_switch("x", vec![("A", 0, inner.clone()), ("B", 0, inner)], None);
    let s = sharing_stats(&tree);
    assert!(s.shared_nodes > 0);
}

#[test]
fn test_sharing_stats_sentinel_leaf() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let s = sharing_stats(&tree);
    assert_eq!(s.total_nodes, 1);
    assert_eq!(s.unique_nodes, 1);
}

#[test]
fn test_sharing_stats_guard_tree() {
    let tree = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(0));
    let s = sharing_stats(&tree);
    assert_eq!(s.total_nodes, 3); // guard + 2 leaves
    assert!(s.shared_nodes > 0); // both leaves are identical
}

// ---------------------------------------------------------------------------
// Branch factor analysis tests
// ---------------------------------------------------------------------------

#[test]
fn test_branch_stats_leaf_only() {
    let tree = DecisionTree::Leaf(0);
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 0);
    assert_eq!(s.min_factor, 0);
    assert_eq!(s.max_factor, 0);
    assert!((s.avg_factor - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_branch_stats_single_switch() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 1);
    assert_eq!(s.min_factor, 2);
    assert_eq!(s.max_factor, 2);
}

#[test]
fn test_branch_stats_with_default() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(1)),
    );
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 1);
    assert_eq!(s.min_factor, 2); // 1 branch + 1 default
    assert_eq!(s.max_factor, 2);
}

#[test]
fn test_branch_stats_nested() {
    let inner = mk_switch(
        "y",
        vec![
            ("C", 0, DecisionTree::Leaf(0)),
            ("D", 0, DecisionTree::Leaf(1)),
            ("E", 0, DecisionTree::Leaf(2)),
        ],
        None,
    );
    let tree = mk_switch("x", vec![("A", 0, inner)], None);
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 2);
    assert_eq!(s.min_factor, 1); // outer: 1 branch
    assert_eq!(s.max_factor, 3); // inner: 3 branches
}

#[test]
fn test_branch_stats_guard_no_switch() {
    let tree = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 0);
}

#[test]
fn test_branch_stats_avg_calculation() {
    // outer: 2 branches, inner: 4 branches => avg = 3.0
    let inner = mk_switch(
        "y",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
            ("C", 0, DecisionTree::Leaf(2)),
            ("D", 0, DecisionTree::Leaf(3)),
        ],
        None,
    );
    let tree = mk_switch(
        "x",
        vec![("E", 0, inner), ("F", 0, DecisionTree::Leaf(4))],
        None,
    );
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 2);
    assert!((s.avg_factor - 3.0).abs() < f64::EPSILON);
}

#[test]
fn test_branch_stats_many_defaults() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(mk_switch("y", vec![], Some(DecisionTree::Leaf(1)))),
    );
    let s = branch_stats(&tree);
    assert_eq!(s.total_switches, 2);
}

// ---------------------------------------------------------------------------
// Path enumeration tests
// ---------------------------------------------------------------------------

#[test]
fn test_enumerate_paths_leaf() {
    let tree = DecisionTree::Leaf(42);
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].0.len(), 0);
    assert_eq!(paths[0].1, 42);
}

#[test]
fn test_enumerate_paths_simple_switch() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 2);
    assert_eq!(
        paths[0].0,
        vec![PathStep::SwitchOn {
            var: mk_var("x"),
            tag: mk_tag("A", 0),
        }]
    );
    assert_eq!(paths[0].1, 0);
    assert_eq!(paths[1].1, 1);
}

#[test]
fn test_enumerate_paths_with_default() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(1)),
    );
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 2);
    // Default path uses __default__ tag
    match &paths[1].0[0] {
        PathStep::SwitchOn { tag, .. } => {
            assert_eq!(tag.name.to_string(), "__default__");
        }
        other => panic!("expected SwitchOn, got {other:?}"),
    }
}

#[test]
fn test_enumerate_paths_guard() {
    let tree = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 2);
    assert_eq!(paths[0].0, vec![PathStep::GuardTrue]);
    assert_eq!(paths[1].0, vec![PathStep::GuardFalse]);
}

#[test]
fn test_enumerate_paths_nested() {
    let inner = mk_switch("y", vec![("C", 0, DecisionTree::Leaf(10))], None);
    let tree = mk_switch("x", vec![("A", 0, inner)], None);
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].0.len(), 2);
    assert_eq!(paths[0].1, 10);
}

#[test]
fn test_enumerate_paths_sentinel() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].1, usize::MAX);
}

#[test]
fn test_enumerate_paths_complex() {
    // Switch x: A -> Guard(Leaf(0), Leaf(1)), B -> Leaf(2)
    let guarded = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let tree = mk_switch(
        "x",
        vec![("A", 0, guarded), ("B", 0, DecisionTree::Leaf(2))],
        None,
    );
    let paths = enumerate_paths(&tree);
    assert_eq!(paths.len(), 3);
}

// ---------------------------------------------------------------------------
// DOT visualization tests
// ---------------------------------------------------------------------------

#[test]
fn test_dot_leaf() {
    let tree = DecisionTree::Leaf(3);
    let dot = tree_to_dot(&tree);
    assert!(dot.contains("digraph DecisionTree"));
    assert!(dot.contains("Leaf 3"));
}

#[test]
fn test_dot_fail_sentinel() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let dot = tree_to_dot(&tree);
    assert!(dot.contains("Leaf fail"));
}

#[test]
fn test_dot_switch() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let dot = tree_to_dot(&tree);
    assert!(dot.contains("Switch x"));
    assert!(dot.contains("shape=ellipse"));
    assert!(dot.contains("[label=\"A\"]"));
    assert!(dot.contains("[label=\"B\"]"));
}

#[test]
fn test_dot_guard() {
    let tree = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let dot = tree_to_dot(&tree);
    assert!(dot.contains("Guard"));
    assert!(dot.contains("shape=diamond"));
    assert!(dot.contains("[label=\"true\"]"));
    assert!(dot.contains("[label=\"false\"]"));
}

#[test]
fn test_dot_default_branch() {
    let tree = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(1)),
    );
    let dot = tree_to_dot(&tree);
    assert!(dot.contains("[label=\"default\"]"));
}

#[test]
fn test_dot_has_edges() {
    let tree = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let dot = tree_to_dot(&tree);
    // Should have at least one edge
    assert!(dot.contains("->"));
}

// ---------------------------------------------------------------------------
// Tree comparison tests
// ---------------------------------------------------------------------------

#[test]
fn test_diff_same_trees() {
    let tree = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    assert_eq!(diff_trees(&tree, &tree), TreeDiff::Same);
}

#[test]
fn test_diff_same_leaves() {
    assert_eq!(
        diff_trees(&DecisionTree::Leaf(5), &DecisionTree::Leaf(5)),
        TreeDiff::Same,
    );
}

#[test]
fn test_diff_different_leaves() {
    let a = DecisionTree::Leaf(0);
    let b = DecisionTree::Leaf(1);
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentLeaf);
}

#[test]
fn test_diff_different_node_kinds() {
    let a = DecisionTree::Leaf(0);
    let b = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentStructure);
}

#[test]
fn test_diff_different_switch_vars() {
    let a = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let b = mk_switch("y", vec![("A", 0, DecisionTree::Leaf(0))], None);
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentStructure);
}

#[test]
fn test_diff_different_branch_count() {
    let a = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let b = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentStructure);
}

#[test]
fn test_diff_subtree_differences() {
    let a = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let b = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(1))], None);
    assert_eq!(diff_trees(&a, &b), TreeDiff::SubtreeDiff);
}

#[test]
fn test_diff_guard_same() {
    let a = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let b = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    assert_eq!(diff_trees(&a, &b), TreeDiff::Same);
}

#[test]
fn test_diff_guard_children_differ() {
    let a = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(1));
    let b = mk_guard(DecisionTree::Leaf(0), DecisionTree::Leaf(2));
    assert_eq!(diff_trees(&a, &b), TreeDiff::SubtreeDiff);
}

#[test]
fn test_diff_default_mismatch() {
    let a = mk_switch(
        "x",
        vec![("A", 0, DecisionTree::Leaf(0))],
        Some(DecisionTree::Leaf(1)),
    );
    let b = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentStructure);
}

#[test]
fn test_diff_different_tags() {
    let a = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let b = mk_switch("x", vec![("B", 0, DecisionTree::Leaf(0))], None);
    assert_eq!(diff_trees(&a, &b), TreeDiff::DifferentStructure);
}

// ---------------------------------------------------------------------------
// Depth-bounded extraction tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_leaf_at_zero_depth() {
    let tree = DecisionTree::Leaf(5);
    let extracted = extract_subtree(&tree, 0);
    assert_eq!(extracted, DecisionTree::Leaf(5));
}

#[test]
fn test_extract_switch_at_zero_depth() {
    let tree = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let extracted = extract_subtree(&tree, 0);
    // At depth 0, switch node is preserved but children are truncated
    match &extracted {
        DecisionTree::Switch(_, branches, _) => {
            assert_eq!(branches[0].1, DecisionTree::Leaf(usize::MAX));
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_extract_preserves_shallow_tree() {
    let tree = mk_switch(
        "x",
        vec![
            ("A", 0, DecisionTree::Leaf(0)),
            ("B", 0, DecisionTree::Leaf(1)),
        ],
        None,
    );
    let extracted = extract_subtree(&tree, 5);
    assert_eq!(extracted, tree);
}

#[test]
fn test_extract_truncates_deep_tree() {
    let deep = mk_switch("z", vec![("D", 0, DecisionTree::Leaf(99))], None);
    let mid = mk_switch("y", vec![("C", 0, deep)], None);
    let tree = mk_switch("x", vec![("A", 0, mid)], None);
    // max_depth=1: outer switch preserved, inner subtrees truncated at depth 1
    let extracted = extract_subtree(&tree, 1);
    match &extracted {
        DecisionTree::Switch(_, branches, _) => {
            // The inner switch should have its children truncated
            match &branches[0].1 {
                DecisionTree::Switch(_, inner_branches, _) => {
                    assert_eq!(inner_branches[0].1, DecisionTree::Leaf(usize::MAX));
                }
                other => panic!("expected inner Switch, got {other:?}"),
            }
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_extract_guard_at_depth_zero() {
    let tree = mk_guard(
        mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None),
        DecisionTree::Leaf(1),
    );
    let extracted = extract_subtree(&tree, 0);
    match &extracted {
        DecisionTree::Guard(_, success, failure) => {
            assert_eq!(success.as_ref(), &DecisionTree::Leaf(usize::MAX));
            assert_eq!(failure.as_ref(), &DecisionTree::Leaf(usize::MAX));
        }
        other => panic!("expected Guard, got {other:?}"),
    }
}

#[test]
fn test_extract_preserves_leaf_deep() {
    // Even at depth 0, a bare leaf is preserved
    let tree = DecisionTree::Leaf(42);
    let extracted = extract_subtree(&tree, 0);
    assert_eq!(extracted, DecisionTree::Leaf(42));
}

// ---------------------------------------------------------------------------
// Variable collection tests
// ---------------------------------------------------------------------------

#[test]
fn test_collect_scrutinees_leaf() {
    let tree = DecisionTree::Leaf(0);
    let vars = collect_scrutinees(&tree);
    assert!(vars.is_empty());
}

#[test]
fn test_collect_scrutinees_single_switch() {
    let tree = mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None);
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name.to_string(), "x");
}

#[test]
fn test_collect_scrutinees_nested_different() {
    let inner = mk_switch("y", vec![("C", 0, DecisionTree::Leaf(0))], None);
    let tree = mk_switch("x", vec![("A", 0, inner)], None);
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 2);
    assert_eq!(vars[0].name.to_string(), "x");
    assert_eq!(vars[1].name.to_string(), "y");
}

#[test]
fn test_collect_scrutinees_duplicate_var() {
    let inner = mk_switch("x", vec![("C", 0, DecisionTree::Leaf(0))], None);
    let tree = mk_switch("x", vec![("A", 0, inner)], None);
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 1); // deduplicated
}

#[test]
fn test_collect_scrutinees_guard_skips() {
    let tree = mk_guard(
        mk_switch("x", vec![("A", 0, DecisionTree::Leaf(0))], None),
        mk_switch("y", vec![("B", 0, DecisionTree::Leaf(1))], None),
    );
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 2);
    assert_eq!(vars[0].name.to_string(), "x");
    assert_eq!(vars[1].name.to_string(), "y");
}

#[test]
fn test_collect_scrutinees_preserves_order() {
    let inner_y = mk_switch("y", vec![("B", 0, DecisionTree::Leaf(0))], None);
    let inner_z = mk_switch("z", vec![("C", 0, DecisionTree::Leaf(1))], None);
    let tree = mk_switch("x", vec![("A", 0, inner_y)], Some(inner_z));
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 3);
    assert_eq!(vars[0].name.to_string(), "x");
    assert_eq!(vars[1].name.to_string(), "y");
    assert_eq!(vars[2].name.to_string(), "z");
}

#[test]
fn test_collect_scrutinees_empty_switch() {
    let tree = DecisionTree::Switch(mk_var("x"), vec![], None);
    let vars = collect_scrutinees(&tree);
    assert_eq!(vars.len(), 1);
}
