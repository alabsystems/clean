// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Types for the knowledge graph: nodes, edges, and their classifications.

use serde::{Deserialize, Serialize};

use crate::types::SourceSystem;

// ---------------------------------------------------------------------------
// ConceptNode
// ---------------------------------------------------------------------------

/// A node in the knowledge graph representing a mathematical concept.
///
/// Each variant carries concept-specific metadata. A single concept may
/// be formalized in multiple proof systems; the `sources` field tracks
/// which systems have a version of this concept.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConceptNode {
    /// A proven mathematical statement.
    Theorem {
        /// Unique node ID.
        id: u32,
        /// Canonical name (e.g., "Nat.add_comm").
        name: String,
        /// Proof systems that have formalized this theorem.
        sources: Vec<SourceSystem>,
        /// Constant indices in the mathverse shard (one per source).
        constant_indices: Vec<u32>,
    },

    /// A mathematical structure (type, algebra, space, etc.).
    Structure {
        /// Unique node ID.
        id: u32,
        /// Canonical name (e.g., "CommRing", "TopologicalSpace").
        name: String,
        /// Proof systems that define this structure.
        sources: Vec<SourceSystem>,
        /// Constant indices in the mathverse shard.
        constant_indices: Vec<u32>,
    },

    /// An unproven mathematical statement.
    Conjecture {
        /// Unique node ID.
        id: u32,
        /// Name (e.g., "Goldbach", "TwinPrime").
        name: String,
        /// Systems where this conjecture is stated.
        sources: Vec<SourceSystem>,
        /// Brief description of the conjecture.
        description: String,
    },

    /// A computational complexity class (P, NP, PSPACE, etc.).
    ComplexityClass {
        /// Unique node ID.
        id: u32,
        /// Canonical name (e.g., "P", "NP", "EXPTIME").
        name: String,
        /// Systems with formal definitions of this class.
        sources: Vec<SourceSystem>,
        /// Known inclusion relationships (e.g., "P subset NP").
        known_inclusions: Vec<String>,
    },

    /// A neural network architecture pattern (ResNet, Transformer, etc.).
    NNArchPattern {
        /// Unique node ID.
        id: u32,
        /// Architecture name (e.g., "ResNet", "Transformer", "MLP").
        name: String,
        /// Systems with verified properties of this architecture.
        sources: Vec<SourceSystem>,
        /// Verified properties (e.g., "Lipschitz bound", "robustness certificate").
        verified_properties: Vec<String>,
    },
}

impl ConceptNode {
    /// Get the unique ID of this node.
    #[must_use]
    pub fn id(&self) -> u32 {
        match self {
            Self::Theorem { id, .. }
            | Self::Structure { id, .. }
            | Self::Conjecture { id, .. }
            | Self::ComplexityClass { id, .. }
            | Self::NNArchPattern { id, .. } => *id,
        }
    }

    /// Get the canonical name of this node.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Theorem { name, .. }
            | Self::Structure { name, .. }
            | Self::Conjecture { name, .. }
            | Self::ComplexityClass { name, .. }
            | Self::NNArchPattern { name, .. } => name,
        }
    }

    /// Get the source systems for this node.
    #[must_use]
    pub fn sources(&self) -> &[SourceSystem] {
        match self {
            Self::Theorem { sources, .. }
            | Self::Structure { sources, .. }
            | Self::Conjecture { sources, .. }
            | Self::ComplexityClass { sources, .. }
            | Self::NNArchPattern { sources, .. } => sources,
        }
    }

    /// Check if this concept is formalized in multiple systems.
    #[must_use]
    pub fn is_multi_system(&self) -> bool {
        self.sources().len() > 1
    }
}

// ---------------------------------------------------------------------------
// ConceptEdge
// ---------------------------------------------------------------------------

/// An edge in the knowledge graph connecting two concepts.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConceptEdge {
    /// Source node ID.
    pub from: u32,
    /// Target node ID.
    pub to: u32,
    /// Relationship type.
    pub kind: EdgeKind,
    /// Confidence score (0.0 to 1.0). 1.0 for proven relationships,
    /// lower for heuristic/analogous links.
    pub confidence: f64,
}

/// Kind of relationship between knowledge graph nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EdgeKind {
    /// A generalizes B (B is a special case of A).
    /// Example: Group generalizes AbelianGroup.
    Generalizes,

    /// A depends on B (A uses B in its statement or proof).
    DependsOn,

    /// A is analogous to B (similar structure, different domain).
    /// Example: FundamentalTheoremOfAlgebra ~ FundamentalTheoremOfCalculus.
    Analogous,

    /// A is the same concept as B in a different proof system.
    /// Example: Lean4's `Nat.add_comm` = Coq's `Nat.add_comm`.
    CrossSystemEquivalent,

    /// A specializes B (A is a special case of B).
    /// Inverse of Generalizes.
    Specializes,

    /// A contains B (module/namespace containment).
    Contains,

    /// A reduces to B (e.g., a problem reduces to a simpler one).
    /// Example: 3-SAT reduces to Vertex Cover.
    ReducesTo,
}
