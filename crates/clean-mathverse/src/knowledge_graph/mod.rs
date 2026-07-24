// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Knowledge graph for cross-system mathematical concept relationships.
//!
//! Tracks theorems, structures, and conjectures across proof systems
//! with typed edges (Generalizes, DependsOn, Analogous). Higher-level
//! than the raw dependency graph in `retrieval::dependency_graph` — this
//! module models semantic relationships between mathematical concepts,
//! not just syntactic constant dependencies.

pub mod graph;
pub mod types;

#[cfg(test)]
mod tests;

pub use graph::KnowledgeGraph;
pub use types::{ConceptEdge, ConceptNode, EdgeKind};
