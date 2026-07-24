// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency graph for walking constant dependencies.
//!
//! Adjacency list representation optimized for forward traversal
//! (given a constant, find everything it depends on) and reverse
//! traversal (given a constant, find everything that depends on it).

use std::collections::{HashSet, VecDeque};

/// Adjacency-list dependency graph over constant indices.
///
/// Edges are directed: an edge from A to B means "A depends on B".
pub struct DependencyGraph {
    /// Forward adjacency: `forward[a]` = constants that `a` depends on.
    forward: Vec<Vec<u32>>,
    /// Reverse adjacency: `reverse[b]` = constants that depend on `b`.
    reverse: Vec<Vec<u32>>,
}

impl DependencyGraph {
    /// Create a new dependency graph with `num_constants` nodes and no edges.
    #[must_use]
    pub fn new(num_constants: usize) -> Self {
        Self {
            forward: vec![Vec::new(); num_constants],
            reverse: vec![Vec::new(); num_constants],
        }
    }

    /// Add a dependency edge: `from` depends on `to`.
    pub fn add_dependency(&mut self, from: u32, to: u32) {
        let f = from as usize;
        let t = to as usize;
        if f < self.forward.len() && t < self.reverse.len() {
            self.forward[f].push(to);
            self.reverse[t].push(from);
        }
    }

    /// Direct dependencies of a constant (one hop forward).
    #[must_use]
    pub fn direct_deps(&self, idx: u32) -> &[u32] {
        self.forward.get(idx as usize).map_or(&[], |v| v.as_slice())
    }

    /// Direct reverse dependencies (constants that depend on `idx`).
    #[must_use]
    pub fn direct_rdeps(&self, idx: u32) -> &[u32] {
        self.reverse.get(idx as usize).map_or(&[], |v| v.as_slice())
    }

    /// Transitive closure of forward dependencies (BFS).
    /// Returns all constants reachable from `idx` via dependency edges,
    /// not including `idx` itself.
    #[must_use]
    pub fn transitive_deps(&self, idx: u32) -> Vec<u32> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(idx);
        visited.insert(idx);

        let mut result = Vec::new();
        while let Some(current) = queue.pop_front() {
            for &dep in self.direct_deps(current) {
                if visited.insert(dep) {
                    result.push(dep);
                    queue.push_back(dep);
                }
            }
        }
        result
    }

    /// Transitive closure of reverse dependencies (BFS).
    /// Returns all constants that transitively depend on `idx`.
    #[must_use]
    pub fn transitive_rdeps(&self, idx: u32) -> Vec<u32> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(idx);
        visited.insert(idx);

        let mut result = Vec::new();
        while let Some(current) = queue.pop_front() {
            for &rdep in self.direct_rdeps(current) {
                if visited.insert(rdep) {
                    result.push(rdep);
                    queue.push_back(rdep);
                }
            }
        }
        result
    }

    /// Number of nodes in the graph.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.forward.len()
    }

    /// Total number of edges.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.forward.iter().map(|v| v.len()).sum()
    }
}
