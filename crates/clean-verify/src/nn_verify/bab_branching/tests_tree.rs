// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BaB tree formalization.

use super::tree::*;

#[test]
fn test_new_tree_has_single_root() {
    let tree = BabTree::new();
    assert_eq!(tree.size(), 1);
    assert_eq!(tree.max_depth(), 0);
    assert_eq!(tree.leaf_count(), 1);
    assert_eq!(tree.internal_count(), 0);
}

#[test]
fn test_root_is_node_zero() {
    let tree = BabTree::new();
    assert_eq!(tree.root().index(), 0);
    let root = tree.get(tree.root()).expect("root should exist");
    assert!(root.neuron_split.is_none());
    assert!(root.parent.is_none());
    assert!(root.direction.is_none());
    assert_eq!(root.depth, 0);
}

#[test]
fn test_split_creates_two_children() {
    let mut tree = BabTree::new();
    let neuron = NeuronId::new(1, 3);
    let (active, inactive) = tree
        .split_node(tree.root(), neuron)
        .expect("split should succeed");

    assert_eq!(tree.size(), 3);
    assert_eq!(tree.leaf_count(), 2);
    assert_eq!(tree.internal_count(), 1);
    assert_eq!(tree.max_depth(), 1);

    // Root should now be an internal node.
    let root = tree.get(tree.root()).expect("root exists");
    assert_eq!(root.neuron_split, Some(neuron));
    assert_eq!(root.active_child, Some(active));
    assert_eq!(root.inactive_child, Some(inactive));

    // Active child.
    let active_node = tree.get(active).expect("active child exists");
    assert_eq!(active_node.direction, Some(SplitDirection::Active));
    assert_eq!(active_node.parent, Some(tree.root()));
    assert_eq!(active_node.depth, 1);

    // Inactive child.
    let inactive_node = tree.get(inactive).expect("inactive child exists");
    assert_eq!(inactive_node.direction, Some(SplitDirection::Inactive));
    assert_eq!(inactive_node.parent, Some(tree.root()));
    assert_eq!(inactive_node.depth, 1);
}

#[test]
fn test_cannot_split_internal_node() {
    let mut tree = BabTree::new();
    let neuron1 = NeuronId::new(0, 0);
    let neuron2 = NeuronId::new(0, 1);
    tree.split_node(tree.root(), neuron1)
        .expect("first split should succeed");

    // Trying to split the root again should fail (it is now internal).
    assert!(tree.split_node(tree.root(), neuron2).is_none());
}

#[test]
fn test_deep_tree_construction() {
    let mut tree = BabTree::new();
    let root = tree.root();

    // Split root.
    let (a1, _) = tree
        .split_node(root, NeuronId::new(0, 0))
        .expect("split root");

    // Split active child.
    let (a2, _) = tree
        .split_node(a1, NeuronId::new(0, 1))
        .expect("split depth 1");

    // Split again.
    let (a3, _) = tree
        .split_node(a2, NeuronId::new(1, 0))
        .expect("split depth 2");

    assert_eq!(tree.max_depth(), 3);
    assert_eq!(tree.size(), 7); // 1 root + 2 + 2 + 2

    let a3_node = tree.get(a3).expect("a3 exists");
    assert_eq!(a3_node.depth, 3);
}

#[test]
fn test_set_result_on_leaf() {
    let mut tree = BabTree::new();
    assert!(tree.set_result(tree.root(), VerificationResult::Safe));

    let root = tree.get(tree.root()).expect("root exists");
    assert_eq!(root.result, Some(VerificationResult::Safe));
}

#[test]
fn test_cannot_set_result_on_internal_node() {
    let mut tree = BabTree::new();
    tree.split_node(tree.root(), NeuronId::new(0, 0))
        .expect("split succeeds");

    // Root is now internal -- setting result should fail.
    assert!(!tree.set_result(tree.root(), VerificationResult::Safe));
}

#[test]
fn test_overall_result_all_safe() {
    let mut tree = BabTree::new();
    let (active, inactive) = tree
        .split_node(tree.root(), NeuronId::new(0, 0))
        .expect("split");

    tree.set_result(active, VerificationResult::Safe);
    tree.set_result(inactive, VerificationResult::Safe);

    assert_eq!(tree.overall_result(), Some(VerificationResult::Safe));
    assert!(tree.is_complete());
}

#[test]
fn test_overall_result_any_unsafe() {
    let mut tree = BabTree::new();
    let (active, inactive) = tree
        .split_node(tree.root(), NeuronId::new(0, 0))
        .expect("split");

    tree.set_result(active, VerificationResult::Safe);
    tree.set_result(inactive, VerificationResult::Unsafe);

    assert_eq!(tree.overall_result(), Some(VerificationResult::Unsafe));
}

#[test]
fn test_overall_result_unknown_when_incomplete() {
    let mut tree = BabTree::new();
    let (active, _inactive) = tree
        .split_node(tree.root(), NeuronId::new(0, 0))
        .expect("split");

    tree.set_result(active, VerificationResult::Safe);
    // inactive has no result yet.

    assert_eq!(tree.overall_result(), None);
    assert!(!tree.is_complete());
}

#[test]
fn test_open_leaves() {
    let mut tree = BabTree::new();
    let (active, inactive) = tree
        .split_node(tree.root(), NeuronId::new(0, 0))
        .expect("split");

    let open = tree.open_leaves();
    assert_eq!(open.len(), 2);

    tree.set_result(active, VerificationResult::Safe);
    let open = tree.open_leaves();
    assert_eq!(open.len(), 1);
    assert_eq!(open[0], inactive);
}

#[test]
fn test_path_to_node() {
    let mut tree = BabTree::new();
    let n0 = NeuronId::new(0, 0);
    let n1 = NeuronId::new(0, 1);
    let n2 = NeuronId::new(1, 0);

    let (active1, _) = tree.split_node(tree.root(), n0).expect("split 0");
    let (_, inactive2) = tree.split_node(active1, n1).expect("split 1");
    let (active3, _) = tree.split_node(inactive2, n2).expect("split 2");

    let path = tree.path_to_node(active3);
    assert_eq!(path.len(), 3);
    assert_eq!(path[0], (n0, SplitDirection::Active));
    assert_eq!(path[1], (n1, SplitDirection::Inactive));
    assert_eq!(path[2], (n2, SplitDirection::Active));
}

#[test]
fn test_path_to_root_is_empty() {
    let tree = BabTree::new();
    let path = tree.path_to_node(tree.root());
    assert!(path.is_empty());
}

#[test]
fn test_neuron_id_equality() {
    let a = NeuronId::new(1, 5);
    let b = NeuronId::new(1, 5);
    let c = NeuronId::new(2, 5);
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn test_set_lower_bound() {
    let mut tree = BabTree::new();
    assert!(tree.set_lower_bound(tree.root(), 0.5));
    let root = tree.get(tree.root()).expect("root exists");
    assert!((root.lower_bound - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_default_tree() {
    let tree = BabTree::default();
    assert_eq!(tree.size(), 1);
}
