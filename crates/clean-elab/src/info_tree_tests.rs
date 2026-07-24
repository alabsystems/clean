// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for info tree construction and querying.

use clean_kernel::{Expr, Level, Name};
use clean_parser::Span;

use crate::info_tree::{query_at_position, InfoData, InfoKind, InfoTree, InfoTreeBuilder};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn prop_sort() -> Expr {
    Expr::sort(Level::zero())
}

fn bool_type() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

// ---------------------------------------------------------------------------
// Construction tests
// ---------------------------------------------------------------------------

#[test]
fn test_info_tree_build_simple_leaf() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(0, 10),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();
    let tree = builder.build();

    // Should be a Node with one Leaf child.
    match &tree {
        InfoTree::Node { node, children } => {
            assert_eq!(node.span, Span::new(0, 10));
            assert_eq!(children.len(), 1);
            assert!(matches!(
                &children[0],
                InfoTree::Leaf(InfoData::TypeAscription(..))
            ));
        }
        _ => panic!("expected Node at root"),
    }
}

#[test]
fn test_info_tree_build_nested_nodes() {
    let mut builder = InfoTreeBuilder::new();

    // Outer node [0, 20)
    builder.push_node(
        Span::new(0, 20),
        InfoKind::CommandInfo {
            command_name: "def".to_owned(),
        },
    );

    // Inner node [5, 15)
    builder.push_node(
        Span::new(5, 15),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();

    builder.pop_node();

    let tree = builder.build();

    match &tree {
        InfoTree::Node { children, .. } => {
            assert_eq!(
                children.len(),
                1,
                "outer node should have one child (inner node)"
            );
            match &children[0] {
                InfoTree::Node {
                    node: inner_node,
                    children: inner_children,
                } => {
                    assert_eq!(inner_node.span, Span::new(5, 15));
                    assert_eq!(inner_children.len(), 1);
                }
                _ => panic!("expected nested Node"),
            }
        }
        _ => panic!("expected Node at root"),
    }
}

#[test]
fn test_info_tree_build_empty_tree() {
    let builder = InfoTreeBuilder::new();
    let tree = builder.build();

    // Empty builder yields a synthetic root node with no children.
    match &tree {
        InfoTree::Node { children, .. } => {
            assert!(children.is_empty(), "empty tree should have no children");
        }
        _ => panic!("expected empty Node"),
    }
}

#[test]
fn test_info_tree_build_multiple_roots() {
    let mut builder = InfoTreeBuilder::new();

    // Two root-level leaves (no enclosing push_node).
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.add_leaf(InfoData::DefinitionHover(
        Name::from_string("foo"),
        prop_sort(),
    ));

    let tree = builder.build();

    // Multiple roots → wrapped in a synthetic root.
    match &tree {
        InfoTree::Node { children, .. } => {
            assert_eq!(children.len(), 2);
        }
        _ => panic!("expected synthetic root Node"),
    }
}

#[test]
fn test_info_tree_build_unclosed_nodes_recovered() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(0, 50),
        InfoKind::CommandInfo {
            command_name: "theorem".to_owned(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(prop_sort(), prop_sort()));
    // Intentionally do NOT call pop_node — builder.build() should recover.
    let tree = builder.build();

    match &tree {
        InfoTree::Node { children, .. } => {
            assert_eq!(children.len(), 1, "unclosed node should still appear");
        }
        _ => panic!("expected Node"),
    }
}

// ---------------------------------------------------------------------------
// Query tests
// ---------------------------------------------------------------------------

#[test]
fn test_query_at_position_finds_matching_leaf() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(10, 20),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();
    let tree = builder.build();

    // Position 15 is inside [10, 20).
    let results = query_at_position(&tree, 15);
    assert_eq!(results.len(), 1);
    assert!(matches!(results[0], InfoData::TypeAscription(..)));
}

#[test]
fn test_query_at_position_misses_out_of_range() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(10, 20),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();
    let tree = builder.build();

    // Position 5 is before the span.
    assert!(query_at_position(&tree, 5).is_empty());

    // Position 20 is at the end (exclusive), so not in range.
    assert!(query_at_position(&tree, 20).is_empty());

    // Position 25 is well beyond.
    assert!(query_at_position(&tree, 25).is_empty());
}

#[test]
fn test_query_at_position_nested_nodes() {
    let mut builder = InfoTreeBuilder::new();

    // Outer [0, 30)
    builder.push_node(
        Span::new(0, 30),
        InfoKind::CommandInfo {
            command_name: "example".to_owned(),
        },
    );
    builder.add_leaf(InfoData::DefinitionHover(
        Name::from_string("example"),
        prop_sort(),
    ));

    // Inner [10, 20)
    builder.push_node(
        Span::new(10, 20),
        InfoKind::TermInfo {
            elaborated: bool_type(),
            type_: prop_sort(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(bool_type(), prop_sort()));
    builder.pop_node();

    builder.pop_node();

    let tree = builder.build();

    // Position 15: inside both outer and inner → should find both leaves.
    let results = query_at_position(&tree, 15);
    assert_eq!(
        results.len(),
        2,
        "should find leaves from both outer and inner nodes"
    );

    // Position 5: inside outer only → should find only the DefinitionHover.
    let results = query_at_position(&tree, 5);
    assert_eq!(results.len(), 1);
    assert!(matches!(results[0], InfoData::DefinitionHover(..)));
}

#[test]
fn test_query_at_position_boundary_start() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(10, 20),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();
    let tree = builder.build();

    // Position 10 is exactly at start (inclusive).
    let results = query_at_position(&tree, 10);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_query_at_position_completion_context() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(0, 10),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    builder.add_leaf(InfoData::CompletionContext(
        Name::from_string("Nat"),
        vec![
            Name::from_string("Nat.add"),
            Name::from_string("Nat.sub"),
            Name::from_string("Nat.mul"),
        ],
    ));
    builder.pop_node();
    let tree = builder.build();

    let results = query_at_position(&tree, 3);
    assert_eq!(results.len(), 1);
    match results[0] {
        InfoData::CompletionContext(ref prefix, ref candidates) => {
            assert_eq!(*prefix, Name::from_string("Nat"));
            assert_eq!(candidates.len(), 3);
        }
        _ => panic!("expected CompletionContext"),
    }
}

#[test]
fn test_query_at_position_tactic_info() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(5, 25),
        InfoKind::TacticInfo {
            goals_before: vec![prop_sort()],
            goals_after: vec![],
        },
    );
    builder.add_leaf(InfoData::TypeAscription(prop_sort(), prop_sort()));
    builder.pop_node();
    let tree = builder.build();

    let results = query_at_position(&tree, 10);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_query_at_position_field_info() {
    let mut builder = InfoTreeBuilder::new();
    builder.push_node(
        Span::new(0, 15),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("Point"),
            field_name: Name::from_string("x"),
        },
    );
    builder.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    builder.pop_node();
    let tree = builder.build();

    let results = query_at_position(&tree, 7);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_query_at_position_empty_tree_returns_nothing() {
    let builder = InfoTreeBuilder::new();
    let tree = builder.build();

    // Empty tree with any position should return nothing.
    assert!(query_at_position(&tree, 0).is_empty());
    assert!(query_at_position(&tree, 100).is_empty());
}
