// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builds KnowledgeGraph nodes and CrossSystemEquivalent edges from cross-system matches.

use std::collections::HashSet;

use crate::cross_system_index::{ConstantRef, EquivalenceMatch};
use crate::knowledge_graph::graph::KnowledgeGraph;
use crate::knowledge_graph::types::{ConceptEdge, ConceptNode, EdgeKind};
use crate::types::SourceSystem;

fn theorem_node(id: u32, constant_ref: &ConstantRef) -> ConceptNode {
    ConceptNode::Theorem {
        id,
        name: constant_ref.original_name.clone(),
        sources: vec![constant_ref.source],
        constant_indices: vec![constant_ref.constant_id],
    }
}

fn primary_source(node: &ConceptNode) -> Option<SourceSystem> {
    node.sources().first().copied()
}

#[must_use]
pub fn build_equiv_graph(matches: &[EquivalenceMatch]) -> (KnowledgeGraph, usize) {
    let mut graph = KnowledgeGraph::new();
    let mut next_id = 0_u32;
    let mut edge_count = 0_usize;

    for equivalence_match in matches.iter().filter(|m| m.system_count >= 2) {
        let mut node_ids = Vec::with_capacity(equivalence_match.refs.len());

        for constant_ref in &equivalence_match.refs {
            let node_id = graph.add_node(theorem_node(next_id, constant_ref));
            next_id += 1;
            node_ids.push(node_id);
        }

        for (index, &from) in node_ids.iter().enumerate() {
            for &to in &node_ids[index + 1..] {
                if from == to {
                    continue;
                }

                graph.add_edge(ConceptEdge {
                    from,
                    to,
                    kind: EdgeKind::CrossSystemEquivalent,
                    confidence: f64::from(equivalence_match.confidence),
                });
                edge_count += 1;
            }
        }
    }

    (graph, edge_count)
}

#[must_use]
pub fn find_equivalents_in_graph(
    graph: &KnowledgeGraph,
    name: &str,
) -> Vec<(String, SourceSystem)> {
    let Some(node) = graph.get_by_name(name) else {
        return Vec::new();
    };

    let node_id = node.id();
    let mut equivalents = Vec::new();
    let mut seen = HashSet::new();

    let outgoing = graph
        .neighbors(node_id)
        .into_iter()
        .filter_map(|(edge, neighbor_id)| {
            (edge.kind == EdgeKind::CrossSystemEquivalent).then_some(neighbor_id)
        });
    let incoming =
        graph
            .incoming_neighbors(node_id)
            .into_iter()
            .filter_map(|(edge, neighbor_id)| {
                (edge.kind == EdgeKind::CrossSystemEquivalent).then_some(neighbor_id)
            });

    for neighbor_id in outgoing.chain(incoming) {
        let Some(neighbor) = graph.get_by_id(neighbor_id) else {
            continue;
        };
        let Some(source) = primary_source(neighbor) else {
            continue;
        };

        let equivalent = (neighbor.name().to_owned(), source);
        if seen.insert(equivalent.clone()) {
            equivalents.push(equivalent);
        }
    }

    equivalents.sort_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then_with(|| (left.1 as u8).cmp(&(right.1 as u8)))
    });
    equivalents
}

#[cfg(test)]
mod tests {
    use super::{build_equiv_graph, find_equivalents_in_graph};
    use crate::cross_system_index::{ConstantRef, EquivalenceMatch};
    use crate::knowledge_graph::types::EdgeKind;
    use crate::types::SourceSystem;

    fn constant_ref(
        source: SourceSystem,
        shard_id: u32,
        constant_id: u32,
        original_name: &str,
    ) -> ConstantRef {
        ConstantRef {
            source,
            shard_id,
            constant_id,
            original_name: original_name.to_owned(),
        }
    }

    fn equivalence_match(
        canonical_name: &str,
        refs: Vec<ConstantRef>,
        system_count: usize,
        confidence: f32,
    ) -> EquivalenceMatch {
        EquivalenceMatch {
            canonical_name: canonical_name.to_owned(),
            refs,
            system_count,
            confidence,
        }
    }

    #[test]
    fn test_build_equiv_graph_basic() {
        let matches = vec![equivalence_match(
            "nat_add_comm",
            vec![
                constant_ref(SourceSystem::Lean4, 0, 1, "Nat.add_comm"),
                constant_ref(SourceSystem::Coq, 1, 2, "PeanoNat.Nat.add_comm"),
            ],
            2,
            0.9,
        )];

        let (graph, edge_count) = build_equiv_graph(&matches);

        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 1);
        assert_eq!(edge_count, 1);
        assert!(graph.get_by_name("Nat.add_comm").is_some());
        assert!(graph.get_by_name("PeanoNat.Nat.add_comm").is_some());

        let edge = graph.edges().first().unwrap();
        assert_eq!(edge.kind, EdgeKind::CrossSystemEquivalent);
        assert!((edge.confidence - 0.9).abs() < 1e-6);
    }

    #[test]
    fn test_build_equiv_graph_three_systems() {
        let matches = vec![equivalence_match(
            "nat_add_assoc",
            vec![
                constant_ref(SourceSystem::Lean4, 0, 1, "Nat.add_assoc"),
                constant_ref(SourceSystem::Coq, 1, 2, "PeanoNat.Nat.add_assoc"),
                constant_ref(SourceSystem::Isabelle, 2, 3, "Groups.add.assoc"),
            ],
            3,
            0.8,
        )];

        let (graph, edge_count) = build_equiv_graph(&matches);

        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);
        assert_eq!(edge_count, 3);
        assert!(graph
            .edges()
            .iter()
            .all(|edge| edge.kind == EdgeKind::CrossSystemEquivalent));
    }

    #[test]
    fn test_find_equivalents() {
        let matches = vec![equivalence_match(
            "nat_add_comm",
            vec![
                constant_ref(SourceSystem::Lean4, 0, 1, "Nat.add_comm"),
                constant_ref(SourceSystem::Coq, 1, 2, "PeanoNat.Nat.add_comm"),
            ],
            2,
            1.0,
        )];
        let (graph, _) = build_equiv_graph(&matches);

        let equivalents = find_equivalents_in_graph(&graph, "PeanoNat.Nat.add_comm");

        assert_eq!(
            equivalents,
            vec![("Nat.add_comm".to_owned(), SourceSystem::Lean4)]
        );
    }

    #[test]
    fn test_find_equivalents_not_found() {
        let matches = vec![equivalence_match(
            "nat_add_comm",
            vec![
                constant_ref(SourceSystem::Lean4, 0, 1, "Nat.add_comm"),
                constant_ref(SourceSystem::Coq, 1, 2, "PeanoNat.Nat.add_comm"),
            ],
            2,
            1.0,
        )];
        let (graph, _) = build_equiv_graph(&matches);

        assert!(find_equivalents_in_graph(&graph, "missing.name").is_empty());
    }
}
