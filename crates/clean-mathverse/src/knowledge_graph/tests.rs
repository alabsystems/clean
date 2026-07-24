// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the knowledge graph module.

use super::graph::KnowledgeGraph;
use super::types::{ConceptEdge, ConceptNode, EdgeKind};
use crate::types::SourceSystem;

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn theorem(id: u32, name: &str, sources: Vec<SourceSystem>) -> ConceptNode {
    ConceptNode::Theorem {
        id,
        name: name.to_owned(),
        sources,
        constant_indices: vec![id],
    }
}

fn structure(id: u32, name: &str, sources: Vec<SourceSystem>) -> ConceptNode {
    ConceptNode::Structure {
        id,
        name: name.to_owned(),
        sources,
        constant_indices: vec![id],
    }
}

fn conjecture(id: u32, name: &str, desc: &str) -> ConceptNode {
    ConceptNode::Conjecture {
        id,
        name: name.to_owned(),
        sources: vec![SourceSystem::Lean4],
        description: desc.to_owned(),
    }
}

fn edge(from: u32, to: u32, kind: EdgeKind) -> ConceptEdge {
    ConceptEdge {
        from,
        to,
        kind,
        confidence: 1.0,
    }
}

// ---------------------------------------------------------------------------
// Node tests
// ---------------------------------------------------------------------------

#[test]
fn test_add_node_theorem() {
    let mut g = KnowledgeGraph::new();
    let id = g.add_node(theorem(0, "Nat.add_comm", vec![SourceSystem::Lean4]));
    assert_eq!(id, 0);
    assert_eq!(g.node_count(), 1);
}

#[test]
fn test_add_node_structure() {
    let mut g = KnowledgeGraph::new();
    let id = g.add_node(structure(
        0,
        "CommRing",
        vec![SourceSystem::Lean4, SourceSystem::Coq],
    ));
    assert_eq!(id, 0);
    let node = g.get_by_name("CommRing").unwrap();
    assert!(node.is_multi_system());
}

#[test]
fn test_add_node_conjecture() {
    let mut g = KnowledgeGraph::new();
    let id = g.add_node(conjecture(
        0,
        "Goldbach",
        "Every even integer > 2 is the sum of two primes",
    ));
    assert_eq!(id, 0);
    let node = g.get_by_id(0).unwrap();
    assert_eq!(node.name(), "Goldbach");
}

#[test]
fn test_add_node_dedup_by_name() {
    let mut g = KnowledgeGraph::new();
    let id1 = g.add_node(theorem(0, "Nat.add_comm", vec![SourceSystem::Lean4]));
    let id2 = g.add_node(theorem(1, "Nat.add_comm", vec![SourceSystem::Coq]));
    assert_eq!(id1, id2);
    assert_eq!(g.node_count(), 1);
}

#[test]
fn test_get_by_name_not_found() {
    let g = KnowledgeGraph::new();
    assert!(g.get_by_name("nonexistent").is_none());
}

// ---------------------------------------------------------------------------
// Edge tests
// ---------------------------------------------------------------------------

#[test]
fn test_add_edge_depends_on() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "Nat.add_comm", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "Nat.add", vec![SourceSystem::Lean4]));
    g.add_edge(edge(0, 1, EdgeKind::DependsOn));

    assert_eq!(g.edge_count(), 1);
    let related = g.query_related(0);
    assert_eq!(related.len(), 1);
    assert_eq!(related[0].1.name(), "Nat.add");
}

#[test]
fn test_add_edge_generalizes() {
    let mut g = KnowledgeGraph::new();
    g.add_node(structure(0, "Group", vec![SourceSystem::Lean4]));
    g.add_node(structure(1, "AbelianGroup", vec![SourceSystem::Lean4]));
    g.add_edge(edge(0, 1, EdgeKind::Generalizes));

    let related = g.query_related_by_kind(0, EdgeKind::Generalizes);
    assert_eq!(related.len(), 1);
    assert_eq!(related[0].1.name(), "AbelianGroup");
}

#[test]
fn test_add_edge_analogous() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "FTA", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "FTC", vec![SourceSystem::Lean4]));
    g.add_edge(ConceptEdge {
        from: 0,
        to: 1,
        kind: EdgeKind::Analogous,
        confidence: 0.7,
    });

    let related = g.query_related_by_kind(0, EdgeKind::Analogous);
    assert_eq!(related.len(), 1);
    assert!((related[0].0.confidence - 0.7).abs() < f64::EPSILON);
}

#[test]
fn test_cross_system_equivalent() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "Lean4.Nat.add_comm", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "Coq.Nat.add_comm", vec![SourceSystem::Coq]));
    g.add_edge(edge(0, 1, EdgeKind::CrossSystemEquivalent));

    let related = g.query_related_by_kind(0, EdgeKind::CrossSystemEquivalent);
    assert_eq!(related.len(), 1);
    assert_eq!(related[0].1.name(), "Coq.Nat.add_comm");
}

// ---------------------------------------------------------------------------
// Query tests
// ---------------------------------------------------------------------------

#[test]
fn test_query_related_empty() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "isolated", vec![SourceSystem::Lean4]));
    let related = g.query_related(0);
    assert!(related.is_empty());
}

#[test]
fn test_query_related_multiple() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "A", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "B", vec![SourceSystem::Lean4]));
    g.add_node(theorem(2, "C", vec![SourceSystem::Lean4]));
    g.add_edge(edge(0, 1, EdgeKind::DependsOn));
    g.add_edge(edge(0, 2, EdgeKind::Generalizes));

    let related = g.query_related(0);
    assert_eq!(related.len(), 2);
}

#[test]
fn test_query_related_by_kind_filters() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "A", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "B", vec![SourceSystem::Lean4]));
    g.add_node(theorem(2, "C", vec![SourceSystem::Lean4]));
    g.add_edge(edge(0, 1, EdgeKind::DependsOn));
    g.add_edge(edge(0, 2, EdgeKind::Generalizes));

    let deps = g.query_related_by_kind(0, EdgeKind::DependsOn);
    assert_eq!(deps.len(), 1);
    assert_eq!(deps[0].1.name(), "B");

    let gens = g.query_related_by_kind(0, EdgeKind::Generalizes);
    assert_eq!(gens.len(), 1);
    assert_eq!(gens[0].1.name(), "C");
}

#[test]
fn test_query_incoming() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "Nat", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "Nat.add", vec![SourceSystem::Lean4]));
    g.add_node(theorem(2, "Nat.mul", vec![SourceSystem::Lean4]));
    g.add_edge(edge(1, 0, EdgeKind::DependsOn));
    g.add_edge(edge(2, 0, EdgeKind::DependsOn));

    let incoming = g.query_incoming(0);
    assert_eq!(incoming.len(), 2);
    let names: Vec<&str> = incoming.iter().map(|(_, n)| n.name()).collect();
    assert!(names.contains(&"Nat.add"));
    assert!(names.contains(&"Nat.mul"));
}

#[test]
fn test_multi_system_concepts() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "single", vec![SourceSystem::Lean4]));
    g.add_node(theorem(
        1,
        "multi",
        vec![SourceSystem::Lean4, SourceSystem::Coq],
    ));
    g.add_node(structure(
        2,
        "Ring",
        vec![
            SourceSystem::Lean4,
            SourceSystem::Isabelle,
            SourceSystem::Coq,
        ],
    ));

    let multi = g.multi_system_concepts();
    assert_eq!(multi.len(), 2);
    let names: Vec<&str> = multi.iter().map(|n| n.name()).collect();
    assert!(names.contains(&"multi"));
    assert!(names.contains(&"Ring"));
}

// ---------------------------------------------------------------------------
// ConceptNode accessor tests
// ---------------------------------------------------------------------------

#[test]
fn test_concept_node_accessors() {
    let t = theorem(42, "thm", vec![SourceSystem::Lean4, SourceSystem::Coq]);
    assert_eq!(t.id(), 42);
    assert_eq!(t.name(), "thm");
    assert_eq!(t.sources().len(), 2);
    assert!(t.is_multi_system());

    let s = structure(10, "Ring", vec![SourceSystem::Lean4]);
    assert_eq!(s.id(), 10);
    assert!(!s.is_multi_system());

    let c = conjecture(99, "P_NP", "P = NP?");
    assert_eq!(c.id(), 99);
    assert_eq!(c.name(), "P_NP");
}

// ---------------------------------------------------------------------------
// ComplexityClass tests
// ---------------------------------------------------------------------------

fn complexity_class(id: u32, name: &str, inclusions: Vec<&str>) -> ConceptNode {
    ConceptNode::ComplexityClass {
        id,
        name: name.to_owned(),
        sources: vec![SourceSystem::Lean4],
        known_inclusions: inclusions.into_iter().map(String::from).collect(),
    }
}

#[test]
fn test_add_complexity_class() {
    let mut g = KnowledgeGraph::new();
    let id = g.add_node(complexity_class(0, "P", vec!["P subset NP"]));
    assert_eq!(id, 0);
    let node = g.get_by_name("P").unwrap();
    assert_eq!(node.name(), "P");
    assert!(!node.is_multi_system());
}

#[test]
fn test_complexity_class_reduces_to() {
    let mut g = KnowledgeGraph::new();
    g.add_node(complexity_class(0, "3-SAT", vec![]));
    g.add_node(complexity_class(1, "VertexCover", vec![]));
    g.add_edge(ConceptEdge {
        from: 0,
        to: 1,
        kind: EdgeKind::ReducesTo,
        confidence: 1.0,
    });

    let reductions = g.query_related_by_kind(0, EdgeKind::ReducesTo);
    assert_eq!(reductions.len(), 1);
    assert_eq!(reductions[0].1.name(), "VertexCover");
}

// ---------------------------------------------------------------------------
// NNArchPattern tests
// ---------------------------------------------------------------------------

fn nn_arch(id: u32, name: &str, properties: Vec<&str>) -> ConceptNode {
    ConceptNode::NNArchPattern {
        id,
        name: name.to_owned(),
        sources: vec![SourceSystem::GammaCrown],
        verified_properties: properties.into_iter().map(String::from).collect(),
    }
}

#[test]
fn test_add_nn_arch_pattern() {
    let mut g = KnowledgeGraph::new();
    let id = g.add_node(nn_arch(
        0,
        "ResNet",
        vec!["Lipschitz bound", "robustness certificate"],
    ));
    assert_eq!(id, 0);
    let node = g.get_by_name("ResNet").unwrap();
    assert_eq!(node.name(), "ResNet");
    if let ConceptNode::NNArchPattern {
        verified_properties,
        ..
    } = node
    {
        assert_eq!(verified_properties.len(), 2);
    } else {
        panic!("expected NNArchPattern variant");
    }
}

#[test]
fn test_nn_arch_depends_on_structure() {
    let mut g = KnowledgeGraph::new();
    g.add_node(nn_arch(0, "Transformer", vec!["attention bounds"]));
    g.add_node(structure(1, "SoftmaxLayer", vec![SourceSystem::GammaCrown]));
    g.add_edge(edge(0, 1, EdgeKind::DependsOn));

    let deps = g.query_related_by_kind(0, EdgeKind::DependsOn);
    assert_eq!(deps.len(), 1);
    assert_eq!(deps[0].1.name(), "SoftmaxLayer");
}

// ---------------------------------------------------------------------------
// neighbors() tests
// ---------------------------------------------------------------------------

#[test]
fn test_neighbors_returns_edge_and_node_id() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "A", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "B", vec![SourceSystem::Lean4]));
    g.add_node(theorem(2, "C", vec![SourceSystem::Lean4]));
    g.add_edge(edge(0, 1, EdgeKind::DependsOn));
    g.add_edge(edge(0, 2, EdgeKind::Generalizes));

    let neighbors = g.neighbors(0);
    assert_eq!(neighbors.len(), 2);
    let target_ids: Vec<u32> = neighbors.iter().map(|(_, id)| *id).collect();
    assert!(target_ids.contains(&1));
    assert!(target_ids.contains(&2));
}

#[test]
fn test_neighbors_empty_for_isolated_node() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "isolated", vec![SourceSystem::Lean4]));
    assert!(g.neighbors(0).is_empty());
}

#[test]
fn test_incoming_neighbors() {
    let mut g = KnowledgeGraph::new();
    g.add_node(theorem(0, "target", vec![SourceSystem::Lean4]));
    g.add_node(theorem(1, "source1", vec![SourceSystem::Lean4]));
    g.add_node(theorem(2, "source2", vec![SourceSystem::Lean4]));
    g.add_edge(edge(1, 0, EdgeKind::DependsOn));
    g.add_edge(edge(2, 0, EdgeKind::DependsOn));

    let incoming = g.incoming_neighbors(0);
    assert_eq!(incoming.len(), 2);
    let source_ids: Vec<u32> = incoming.iter().map(|(_, id)| *id).collect();
    assert!(source_ids.contains(&1));
    assert!(source_ids.contains(&2));
}
