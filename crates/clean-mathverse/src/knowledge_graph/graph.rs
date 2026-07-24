// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Knowledge graph implementation: add_node, add_edge, query_related.

use std::collections::HashMap;

use super::types::{ConceptEdge, ConceptNode, EdgeKind};

/// Knowledge graph tracking mathematical concepts and their relationships.
///
/// Nodes are [`ConceptNode`] variants (Theorem, Structure, Conjecture).
/// Edges are typed by [`EdgeKind`] (Generalizes, DependsOn, Analogous, etc.).
///
/// Supports:
/// - O(1) node lookup by ID
/// - O(1) name-to-ID lookup
/// - O(degree) outgoing/incoming edge queries
/// - Filtered queries by edge kind
pub struct KnowledgeGraph {
    nodes: Vec<ConceptNode>,
    name_to_id: HashMap<String, u32>,
    /// Forward adjacency: node_id -> edge indices.
    forward: HashMap<u32, Vec<usize>>,
    /// Reverse adjacency: node_id -> edge indices (edges pointing TO this node).
    reverse: HashMap<u32, Vec<usize>>,
    edges: Vec<ConceptEdge>,
}

impl KnowledgeGraph {
    /// Create a new empty knowledge graph.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            name_to_id: HashMap::new(),
            forward: HashMap::new(),
            reverse: HashMap::new(),
            edges: Vec::new(),
        }
    }

    /// Add a node to the graph. Returns the node's ID.
    ///
    /// If a node with the same name already exists, returns the existing ID
    /// without adding a duplicate.
    pub fn add_node(&mut self, node: ConceptNode) -> u32 {
        let name = node.name().to_owned();
        if let Some(&existing_id) = self.name_to_id.get(&name) {
            return existing_id;
        }
        let id = node.id();
        self.name_to_id.insert(name, id);
        self.nodes.push(node);
        id
    }

    /// Add an edge between two nodes.
    pub fn add_edge(&mut self, edge: ConceptEdge) {
        let idx = self.edges.len();
        self.forward.entry(edge.from).or_default().push(idx);
        self.reverse.entry(edge.to).or_default().push(idx);
        self.edges.push(edge);
    }

    /// Look up a node by name.
    #[must_use]
    pub fn get_by_name(&self, name: &str) -> Option<&ConceptNode> {
        self.name_to_id
            .get(name)
            .and_then(|&id| self.nodes.iter().find(|n| n.id() == id))
    }

    /// Look up a node by ID.
    #[must_use]
    pub fn get_by_id(&self, id: u32) -> Option<&ConceptNode> {
        self.nodes.iter().find(|n| n.id() == id)
    }

    /// Get all concepts related to a node (all outgoing edges).
    #[must_use]
    pub fn query_related(&self, node_id: u32) -> Vec<(&ConceptEdge, &ConceptNode)> {
        self.forward
            .get(&node_id)
            .map(|indices| {
                indices
                    .iter()
                    .filter_map(|&i| {
                        let edge = &self.edges[i];
                        self.get_by_id(edge.to).map(|node| (edge, node))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get related concepts filtered by edge kind.
    #[must_use]
    pub fn query_related_by_kind(
        &self,
        node_id: u32,
        kind: EdgeKind,
    ) -> Vec<(&ConceptEdge, &ConceptNode)> {
        self.query_related(node_id)
            .into_iter()
            .filter(|(edge, _)| edge.kind == kind)
            .collect()
    }

    /// Get all nodes that point TO this node (incoming edges).
    #[must_use]
    pub fn query_incoming(&self, node_id: u32) -> Vec<(&ConceptEdge, &ConceptNode)> {
        self.reverse
            .get(&node_id)
            .map(|indices| {
                indices
                    .iter()
                    .filter_map(|&i| {
                        let edge = &self.edges[i];
                        self.get_by_id(edge.from).map(|node| (edge, node))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Number of nodes.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// All nodes in the graph.
    #[must_use]
    pub fn nodes(&self) -> &[ConceptNode] {
        &self.nodes
    }

    /// All edges in the graph.
    #[must_use]
    pub fn edges(&self) -> &[ConceptEdge] {
        &self.edges
    }

    /// Find all multi-system concepts (formalized in >1 proof system).
    #[must_use]
    pub fn multi_system_concepts(&self) -> Vec<&ConceptNode> {
        self.nodes.iter().filter(|n| n.is_multi_system()).collect()
    }

    /// Get all neighbors of a node (outgoing edges with target node IDs).
    ///
    /// Returns `(edge, target_node_id)` pairs for graph traversal.
    #[must_use]
    pub fn neighbors(&self, node_id: u32) -> Vec<(&ConceptEdge, u32)> {
        self.forward
            .get(&node_id)
            .map(|indices| {
                indices
                    .iter()
                    .map(|&i| (&self.edges[i], self.edges[i].to))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get all incoming neighbors (nodes that point to this node).
    ///
    /// Returns `(edge, source_node_id)` pairs.
    #[must_use]
    pub fn incoming_neighbors(&self, node_id: u32) -> Vec<(&ConceptEdge, u32)> {
        self.reverse
            .get(&node_id)
            .map(|indices| {
                indices
                    .iter()
                    .map(|&i| (&self.edges[i], self.edges[i].from))
                    .collect()
            })
            .unwrap_or_default()
    }
}

impl Default for KnowledgeGraph {
    fn default() -> Self {
        Self::new()
    }
}
