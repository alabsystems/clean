// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Knowledge graph for the Mathverse Library.
//!
//! Models relationships between mathematical concepts across proof systems:
//! - Dependency edges (A uses B)
//! - Equivalence edges (Lean4's X ↔ Coq's Y)
//! - Hierarchy edges (Nat ⊂ Int ⊂ Rat)
//! - Source attribution (which system proved this)

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// ─── Node ────────────────────────────────────────────────────────────────

/// A node in the Mathverse knowledge graph (a mathematical concept).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConceptNode {
    /// Unique concept ID.
    pub id: u32,
    /// Canonical name (e.g., "Nat.add_comm").
    pub name: String,
    /// Category of the concept.
    pub category: ConceptCategory,
    /// Source systems that have formalized this concept.
    pub sources: Vec<SourceSystem>,
    /// Best trust level across all formalizations.
    pub best_trust: TrustLevel,
    /// Combined axiom profile (union of all formalizations).
    pub axiom_profile: AxiomProfile,
}

/// Category of a mathematical concept.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConceptCategory {
    /// A type or data type (Nat, List, etc.)
    Type,
    /// A function or operation (add, mul, etc.)
    Function,
    /// A proposition or theorem statement.
    Proposition,
    /// A proof or evidence term.
    Proof,
    /// A typeclass or interface.
    Typeclass,
    /// A tactic or automation.
    Tactic,
    /// An axiom or postulate.
    Axiom,
}

// ─── Edge ────────────────────────────────────────────────────────────────

/// An edge in the knowledge graph.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConceptEdge {
    /// Source concept.
    pub from: u32,
    /// Target concept.
    pub to: u32,
    /// Relationship type.
    pub kind: EdgeKind,
    /// Confidence in this edge (0.0 to 1.0).
    pub confidence: f64,
}

/// Kind of relationship between concepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EdgeKind {
    /// A depends on B (uses it in proof/definition).
    Depends,
    /// A is equivalent to B (cross-system theorem alignment).
    Equivalent,
    /// A generalizes B (B is a special case of A).
    Generalizes,
    /// A refines/specializes B.
    Specializes,
    /// A contains B (module containment).
    Contains,
    /// A is an instance of typeclass B.
    InstanceOf,
}

// ─── Knowledge graph ─────────────────────────────────────────────────────

/// The Mathverse knowledge graph tracking concepts and their relationships.
pub struct KnowledgeGraph {
    nodes: Vec<ConceptNode>,
    edges: Vec<ConceptEdge>,
    name_index: HashMap<String, u32>,
    adjacency: HashMap<u32, Vec<usize>>,
}

impl KnowledgeGraph {
    /// Create a new empty graph.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            name_index: HashMap::new(),
            adjacency: HashMap::new(),
        }
    }

    /// Add a concept node.
    pub fn add_concept(
        &mut self,
        name: &str,
        category: ConceptCategory,
        source: SourceSystem,
        trust: TrustLevel,
        profile: AxiomProfile,
    ) -> u32 {
        if let Some(&id) = self.name_index.get(name) {
            // Merge: add source and upgrade trust.
            let node = &mut self.nodes[id as usize];
            if !node.sources.contains(&source) {
                node.sources.push(source);
            }
            if trust < node.best_trust {
                node.best_trust = trust;
            }
            node.axiom_profile = node.axiom_profile.union(profile);
            return id;
        }

        let id = self.nodes.len() as u32;
        self.nodes.push(ConceptNode {
            id,
            name: name.to_owned(),
            category,
            sources: vec![source],
            best_trust: trust,
            axiom_profile: profile,
        });
        self.name_index.insert(name.to_owned(), id);
        id
    }

    /// Add an edge between two concepts.
    pub fn add_edge(&mut self, from: u32, to: u32, kind: EdgeKind, confidence: f64) {
        let edge_idx = self.edges.len();
        self.edges.push(ConceptEdge {
            from,
            to,
            kind,
            confidence,
        });
        self.adjacency.entry(from).or_default().push(edge_idx);
    }

    /// Look up a concept by name.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&ConceptNode> {
        self.name_index
            .get(name)
            .map(|&id| &self.nodes[id as usize])
    }

    /// Get all outgoing edges from a concept.
    #[must_use]
    pub fn outgoing_edges(&self, concept_id: u32) -> Vec<&ConceptEdge> {
        self.adjacency
            .get(&concept_id)
            .map(|indices| indices.iter().map(|&i| &self.edges[i]).collect())
            .unwrap_or_default()
    }

    /// Get all concepts reachable by dependency edges from a concept.
    #[must_use]
    pub fn transitive_dependencies(&self, concept_id: u32) -> Vec<u32> {
        let mut visited = std::collections::HashSet::new();
        let mut stack = vec![concept_id];
        let mut result = Vec::new();

        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            if id != concept_id {
                result.push(id);
            }
            for edge in self.outgoing_edges(id) {
                if edge.kind == EdgeKind::Depends {
                    stack.push(edge.to);
                }
            }
        }
        result
    }

    /// Find all cross-system equivalences for a concept.
    #[must_use]
    pub fn equivalences(&self, concept_id: u32) -> Vec<&ConceptNode> {
        let mut result = Vec::new();
        for edge in self.outgoing_edges(concept_id) {
            if edge.kind == EdgeKind::Equivalent {
                result.push(&self.nodes[edge.to as usize]);
            }
        }
        // Check reverse edges too.
        for edge in &self.edges {
            if edge.to == concept_id && edge.kind == EdgeKind::Equivalent {
                result.push(&self.nodes[edge.from as usize]);
            }
        }
        result
    }

    /// Number of concepts.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Concepts formalized in multiple systems.
    #[must_use]
    pub fn multi_system_concepts(&self) -> Vec<&ConceptNode> {
        self.nodes.iter().filter(|n| n.sources.len() > 1).collect()
    }

    /// Concepts at the given trust level.
    #[must_use]
    pub fn concepts_at_trust(&self, level: TrustLevel) -> Vec<&ConceptNode> {
        self.nodes
            .iter()
            .filter(|n| n.best_trust == level)
            .collect()
    }

    /// Summary statistics.
    #[must_use]
    pub fn summary(&self) -> GraphSummary {
        let mut by_category = HashMap::new();
        let mut by_source = HashMap::new();
        let multi_system = self.multi_system_concepts().len();

        for node in &self.nodes {
            *by_category.entry(node.category).or_insert(0usize) += 1;
            for source in &node.sources {
                *by_source.entry(*source).or_insert(0usize) += 1;
            }
        }

        let mut by_edge_kind = HashMap::new();
        for edge in &self.edges {
            *by_edge_kind.entry(edge.kind).or_insert(0usize) += 1;
        }

        GraphSummary {
            node_count: self.nodes.len(),
            edge_count: self.edges.len(),
            multi_system_count: multi_system,
            by_category,
            by_source,
            by_edge_kind,
        }
    }
}

impl Default for KnowledgeGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Summary statistics for the knowledge graph.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GraphSummary {
    pub node_count: usize,
    pub edge_count: usize,
    pub multi_system_count: usize,
    pub by_category: HashMap<ConceptCategory, usize>,
    pub by_source: HashMap<SourceSystem, usize>,
    pub by_edge_kind: HashMap<EdgeKind, usize>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_concept() {
        let mut g = KnowledgeGraph::new();
        let id = g.add_concept(
            "Nat.add_comm",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        assert_eq!(id, 0);
        assert_eq!(g.node_count(), 1);
    }

    #[test]
    fn test_add_concept_merge() {
        let mut g = KnowledgeGraph::new();
        g.add_concept(
            "add_comm",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        g.add_concept(
            "add_comm",
            ConceptCategory::Proposition,
            SourceSystem::Coq,
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::NONE,
        );
        assert_eq!(g.node_count(), 1);
        let node = g.lookup("add_comm").unwrap();
        assert_eq!(node.sources.len(), 2);
        assert_eq!(node.best_trust, TrustLevel::KernelVerified);
    }

    #[test]
    fn test_add_edge_dependency() {
        let mut g = KnowledgeGraph::new();
        let a = g.add_concept(
            "A",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        let b = g.add_concept(
            "B",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        g.add_edge(a, b, EdgeKind::Depends, 1.0);
        assert_eq!(g.edge_count(), 1);
        assert_eq!(g.outgoing_edges(a).len(), 1);
    }

    #[test]
    fn test_transitive_dependencies() {
        let mut g = KnowledgeGraph::new();
        let a = g.add_concept(
            "A",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        let b = g.add_concept(
            "B",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        let c = g.add_concept(
            "C",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        g.add_edge(a, b, EdgeKind::Depends, 1.0);
        g.add_edge(b, c, EdgeKind::Depends, 1.0);

        let deps = g.transitive_dependencies(a);
        assert!(deps.contains(&b));
        assert!(deps.contains(&c));
    }

    #[test]
    fn test_multi_system_concepts() {
        let mut g = KnowledgeGraph::new();
        g.add_concept(
            "add_comm",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        g.add_concept(
            "add_comm",
            ConceptCategory::Proposition,
            SourceSystem::Coq,
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::NONE,
        );
        g.add_concept(
            "singleton",
            ConceptCategory::Type,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );

        let multi = g.multi_system_concepts();
        assert_eq!(multi.len(), 1);
        assert_eq!(multi[0].name, "add_comm");
    }

    #[test]
    fn test_summary() {
        let mut g = KnowledgeGraph::new();
        g.add_concept(
            "A",
            ConceptCategory::Proposition,
            SourceSystem::Lean4,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        );
        g.add_concept(
            "B",
            ConceptCategory::Type,
            SourceSystem::Coq,
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::NONE,
        );
        g.add_edge(0, 1, EdgeKind::Depends, 1.0);

        let summary = g.summary();
        assert_eq!(summary.node_count, 2);
        assert_eq!(summary.edge_count, 1);
    }
}
