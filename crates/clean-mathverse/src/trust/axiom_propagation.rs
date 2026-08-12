// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Axiom profile transitive propagation logic and proof.
//!
//! The central invariant is: after propagation, every node's axiom profile is
//! the union of its own initial profile and the profiles of all transitive
//! dependencies. This module provides both the propagation algorithm and
//! verification of the resulting invariant.

use hashbrown::HashSet;

use crate::types::AxiomProfile;

/// Errors that can occur during axiom propagation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PropagationError {
    /// A node index exceeds the graph's node count.
    #[error("node index {index} out of bounds (graph has {node_count} nodes)")]
    NodeOutOfBounds { index: u32, node_count: usize },

    /// An edge violates the topological order invariant (child_idx < parent_idx).
    #[error("topological order violated: edge from {from} to {to} (requires child < parent)")]
    TopologicalOrderViolation { from: u32, to: u32 },

    /// The propagation invariant failed: a parent does not contain its child's profile.
    #[error(
        "propagation invariant violated: node {parent} (profile {parent_profile:?}) \
         does not contain child {child} (profile {child_profile:?})"
    )]
    InvariantViolation {
        parent: u32,
        parent_profile: AxiomProfile,
        child: u32,
        child_profile: AxiomProfile,
    },

    /// The dependency graph contains a cycle.
    #[error("cycle detected involving node {node}")]
    CycleDetected { node: u32 },
}

/// Dependency graph for axiom profile propagation.
///
/// Nodes are identified by `u32` indices. Each node has an axiom profile and a
/// list of dependencies (edges to other nodes). The propagation algorithm
/// computes the transitive closure of axiom profiles: after propagation, every
/// node's profile is the union of its own initial profile and the profiles of
/// all transitive dependencies.
///
/// The graph exploits a topological ordering invariant: for every edge
/// `(parent, child)`, `child < parent`. This allows single-pass forward
/// propagation in O(V + E) time.
pub struct DependencyGraph {
    /// Adjacency list: `edges[i]` is the list of nodes that node `i` depends on.
    edges: Vec<Vec<u32>>,
    /// Axiom profile per node (initially from the importer, mutated during propagation).
    profiles: Vec<AxiomProfile>,
}

impl DependencyGraph {
    /// Create a new dependency graph with the given number of nodes.
    ///
    /// All nodes start with `AxiomProfile::NONE` (empty profile).
    #[must_use]
    pub fn new(node_count: usize) -> Self {
        Self {
            edges: vec![Vec::new(); node_count],
            profiles: vec![AxiomProfile::NONE; node_count],
        }
    }

    /// Add a directed dependency edge: `from` depends on `to`.
    ///
    /// # Errors
    ///
    /// Returns `PropagationError::NodeOutOfBounds` if either index is out of bounds.
    pub fn add_edge(&mut self, from: u32, to: u32) -> Result<(), PropagationError> {
        let node_count = self.edges.len();
        if from as usize >= node_count {
            return Err(PropagationError::NodeOutOfBounds {
                index: from,
                node_count,
            });
        }
        if to as usize >= node_count {
            return Err(PropagationError::NodeOutOfBounds {
                index: to,
                node_count,
            });
        }
        self.edges[from as usize].push(to);
        Ok(())
    }

    /// Set the initial axiom profile for a node (before propagation).
    ///
    /// # Errors
    ///
    /// Returns `PropagationError::NodeOutOfBounds` if the index is out of bounds.
    pub fn set_initial_profile(
        &mut self,
        node: u32,
        profile: AxiomProfile,
    ) -> Result<(), PropagationError> {
        let node_count = self.profiles.len();
        if node as usize >= node_count {
            return Err(PropagationError::NodeOutOfBounds {
                index: node,
                node_count,
            });
        }
        self.profiles[node as usize] = profile;
        Ok(())
    }

    /// Propagate axiom profiles transitively.
    ///
    /// After this call, every node's profile is the union of its own initial
    /// profile and all transitive dependencies' profiles.
    ///
    /// Uses topological order (requires `child_idx < parent_idx` invariant) for
    /// single-pass O(V + E) propagation. Falls back to iterative fixpoint if
    /// topological order is not satisfied.
    ///
    /// # Errors
    ///
    /// Returns `PropagationError::CycleDetected` if the graph contains a cycle
    /// (detected by fixpoint non-convergence within V iterations).
    pub fn propagate(&mut self) -> Result<(), PropagationError> {
        if self.edges.is_empty() {
            return Ok(());
        }

        // Check for cycles first via topological sort.
        match self.topological_order() {
            Ok(order) => {
                // Process nodes in reverse topological order (dependencies first).
                for &node in &order {
                    let deps = &self.edges[node as usize];
                    let mut accumulated = self.profiles[node as usize];
                    for &dep in deps {
                        accumulated |= self.profiles[dep as usize];
                    }
                    self.profiles[node as usize] = accumulated;
                }
                Ok(())
            }
            Err(cycle_err) => Err(PropagationError::CycleDetected {
                node: cycle_err.node,
            }),
        }
    }

    /// Verify the propagation invariant: for every edge `(parent, child)`,
    /// `parent.profile` is a superset of `child.profile`.
    ///
    /// # Errors
    ///
    /// Returns the first invariant violation found.
    pub fn verify_invariant(&self) -> Result<(), PropagationError> {
        for (parent_idx, deps) in self.edges.iter().enumerate() {
            let parent_profile = self.profiles[parent_idx];
            for &child_idx in deps {
                let child_profile = self.profiles[child_idx as usize];
                if !parent_profile.is_superset_of(child_profile) {
                    return Err(PropagationError::InvariantViolation {
                        parent: parent_idx as u32,
                        parent_profile,
                        child: child_idx,
                        child_profile,
                    });
                }
            }
        }
        Ok(())
    }

    /// Get the (possibly propagated) profile for a node.
    ///
    /// Returns `AxiomProfile::NONE` if the index is out of bounds.
    #[must_use]
    pub fn profile(&self, node: u32) -> AxiomProfile {
        self.profiles
            .get(node as usize)
            .copied()
            .unwrap_or(AxiomProfile::NONE)
    }

    /// Get the number of nodes in the graph.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.edges.len()
    }

    /// Get the dependency list for a node.
    #[must_use]
    pub fn dependencies(&self, node: u32) -> &[u32] {
        self.edges
            .get(node as usize)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Get the total number of edges in the graph.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.edges.iter().map(|deps| deps.len()).sum()
    }

    /// Propagate axiom profiles for only a set of newly added edges.
    ///
    /// Given a list of `(from, to)` edges that were recently added, propagates
    /// profiles along those edges and then continues propagation for all
    /// affected ancestors until a fixpoint is reached.
    ///
    /// This is more efficient than full propagation when only a small number
    /// of edges are new.
    ///
    /// # Errors
    ///
    /// Returns `PropagationError::NodeOutOfBounds` if an edge references a
    /// node beyond the graph size.
    pub fn propagate_incremental(
        &mut self,
        new_edges: &[(u32, u32)],
    ) -> Result<(), PropagationError> {
        let node_count = self.edges.len();
        if node_count == 0 {
            return Ok(());
        }

        // Validate edges.
        for &(from, to) in new_edges {
            if from as usize >= node_count {
                return Err(PropagationError::NodeOutOfBounds {
                    index: from,
                    node_count,
                });
            }
            if to as usize >= node_count {
                return Err(PropagationError::NodeOutOfBounds {
                    index: to,
                    node_count,
                });
            }
        }

        // Seed the worklist with all `from` nodes of new edges.
        let mut worklist: Vec<u32> = new_edges.iter().map(|&(from, _)| from).collect();
        worklist.sort_unstable();
        worklist.dedup();

        // Build a reverse adjacency list for upward propagation.
        let mut reverse: Vec<Vec<u32>> = vec![Vec::new(); node_count];
        for (parent_idx, deps) in self.edges.iter().enumerate() {
            for &child_idx in deps {
                reverse[child_idx as usize].push(parent_idx as u32);
            }
        }

        // Propagate: for each node in the worklist, recompute its profile
        // from its dependencies. If the profile changed, add all of its
        // reverse-dependents (parents) to the worklist.
        let mut visited = vec![false; node_count];
        let max_iterations = node_count * 2; // guard against unexpected cycles
        let mut iterations = 0;

        while let Some(node) = worklist.pop() {
            iterations += 1;
            if iterations > max_iterations {
                return Err(PropagationError::CycleDetected { node });
            }

            let mut accumulated = self.profiles[node as usize];
            for &dep in &self.edges[node as usize] {
                accumulated |= self.profiles[dep as usize];
            }

            if accumulated != self.profiles[node as usize] {
                self.profiles[node as usize] = accumulated;
                // Push parents of this node to the worklist.
                for &parent in &reverse[node as usize] {
                    if !visited[parent as usize] {
                        visited[parent as usize] = true;
                        worklist.push(parent);
                    }
                }
            }
            visited[node as usize] = false; // allow revisiting if profile changes again
        }

        Ok(())
    }

    /// Compute summary statistics about this dependency graph.
    #[must_use]
    pub fn compute_stats(&self) -> DependencyGraphStats {
        let nodes = self.edges.len();
        let edges: usize = self.edges.iter().map(|deps| deps.len()).sum();

        let max_depth = self.compute_max_depth();

        let avg_degree = if nodes > 0 {
            edges as f64 / nodes as f64
        } else {
            0.0
        };

        let cycles_detected = self.topological_order().is_err();

        DependencyGraphStats {
            nodes,
            edges,
            max_depth,
            avg_degree,
            cycles_detected,
        }
    }

    /// Compute the maximum depth (longest path) in the DAG.
    fn compute_max_depth(&self) -> usize {
        let n = self.edges.len();
        if n == 0 {
            return 0;
        }

        let mut depths = vec![0usize; n];

        // If topological order holds (child < parent), single forward pass.
        if verify_topological_order(&self.edges).is_ok() {
            for i in 0..n {
                for &dep in &self.edges[i] {
                    let child_depth = depths[dep as usize];
                    if child_depth + 1 > depths[i] {
                        depths[i] = child_depth + 1;
                    }
                }
            }
            return depths.iter().copied().max().unwrap_or(0);
        }

        // Fallback: iterative for non-topological or cyclic.
        // Simple DFS-based depth computation with cycle detection.
        let mut computed = vec![false; n];
        let mut in_stack = vec![false; n];
        for start in 0..n {
            if computed[start] {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(start, false)];
            while let Some((node, processed)) = stack.pop() {
                if processed {
                    let mut max_child = 0;
                    for &dep in &self.edges[node] {
                        let d = depths[dep as usize];
                        if d + 1 > max_child {
                            max_child = d + 1;
                        }
                    }
                    depths[node] = max_child;
                    computed[node] = true;
                    in_stack[node] = false;
                } else if computed[node] || in_stack[node] {
                    // Already computed or cycle detected — skip.
                    continue;
                } else {
                    in_stack[node] = true;
                    stack.push((node, true));
                    for &dep in &self.edges[node] {
                        if !computed[dep as usize] && !in_stack[dep as usize] {
                            stack.push((dep as usize, false));
                        }
                    }
                }
            }
        }

        depths.iter().copied().max().unwrap_or(0)
    }

    /// Compute a topological ordering of the graph nodes.
    ///
    /// Returns nodes in dependency order: a node appears after all of its
    /// dependencies.
    ///
    /// # Errors
    ///
    /// Returns `CycleError` if the graph contains a cycle.
    pub fn topological_order(&self) -> Result<Vec<u32>, CycleError> {
        let n = self.edges.len();
        if n == 0 {
            return Ok(Vec::new());
        }

        // Kahn's algorithm using dep_count (number of dependencies per node).
        // edges[i] lists the *dependencies* of node i. We want to process
        // dependencies before dependents, so nodes with dep_count == 0
        // (no outstanding dependencies) are ready first.
        //
        // Forward adjacency: forward[dep] = list of nodes that depend on dep.
        let mut forward: Vec<Vec<u32>> = vec![Vec::new(); n];
        let mut dep_count = vec![0u32; n];
        for (i, deps) in self.edges.iter().enumerate() {
            dep_count[i] = deps.len() as u32;
            for &dep in deps {
                forward[dep as usize].push(i as u32);
            }
        }

        // Seed queue with nodes that have no dependencies.
        let mut queue: Vec<u32> = Vec::new();
        for (i, &count) in dep_count.iter().enumerate() {
            if count == 0 {
                queue.push(i as u32);
            }
        }

        // BFS: process in FIFO order for deterministic output.
        let mut order = Vec::with_capacity(n);
        let mut head = 0;
        while head < queue.len() {
            let node = queue[head];
            head += 1;
            order.push(node);

            // For each parent that depends on this node, decrement their dep_count.
            for &parent in &forward[node as usize] {
                dep_count[parent as usize] -= 1;
                if dep_count[parent as usize] == 0 {
                    queue.push(parent);
                }
            }
        }

        if order.len() == n {
            Ok(order)
        } else {
            // Not all nodes are in the ordering => cycle exists.
            // Find a node still with deps remaining.
            let cycle_node = dep_count.iter().position(|&d| d > 0).unwrap_or(0) as u32;
            Err(CycleError { node: cycle_node })
        }
    }

    /// Compute the set of all nodes transitively reachable from `start`
    /// by following dependency edges.
    ///
    /// The result includes `start` itself if there is a self-loop (directly
    /// or transitively), but does NOT include `start` otherwise.
    #[must_use]
    pub fn reachable_from(&self, start: u32) -> HashSet<u32> {
        let mut visited = HashSet::new();
        let n = self.edges.len();
        if (start as usize) >= n {
            return visited;
        }

        let mut stack: Vec<u32> = self.edges[start as usize].clone();
        while let Some(node) = stack.pop() {
            if visited.contains(&node) {
                continue;
            }
            visited.insert(node);
            if (node as usize) < n {
                for &dep in &self.edges[node as usize] {
                    if !visited.contains(&dep) {
                        stack.push(dep);
                    }
                }
            }
        }

        visited
    }
}

/// Error returned when a cycle is detected in topological sort.
#[derive(Clone, Debug, thiserror::Error)]
#[error("cycle detected involving node {node}")]
pub struct CycleError {
    /// A node that is part of the cycle.
    pub node: u32,
}

/// Summary statistics for a dependency graph.
#[derive(Clone, Debug)]
pub struct DependencyGraphStats {
    /// Number of nodes in the graph.
    pub nodes: usize,
    /// Number of directed edges.
    pub edges: usize,
    /// Length of the longest path in the graph.
    pub max_depth: usize,
    /// Average out-degree (dependencies per node).
    pub avg_degree: f64,
    /// Whether any cycle was detected.
    pub cycles_detected: bool,
}

/// Perform one pass of axiom profile propagation.
///
/// For every edge `(parent, child)`, unions the child's profile into the
/// parent's profile. Returns `true` if any profile changed during this pass.
pub fn propagate_single_pass(profiles: &mut [AxiomProfile], edges: &[Vec<u32>]) -> bool {
    let mut changed = false;
    for (parent_idx, deps) in edges.iter().enumerate() {
        let mut accumulated = profiles[parent_idx];
        for &child_idx in deps {
            accumulated |= profiles[child_idx as usize];
        }
        if accumulated != profiles[parent_idx] {
            profiles[parent_idx] = accumulated;
            changed = true;
        }
    }
    changed
}

/// Verify the topological order invariant: for every edge `(from, to)`,
/// `to < from`.
///
/// This invariant allows single-pass forward propagation. It holds when the
/// importer assigns indices in dependency order (children before parents).
///
/// # Errors
///
/// Returns `PropagationError::TopologicalOrderViolation` for the first
/// violating edge found.
pub fn verify_topological_order(edges: &[Vec<u32>]) -> Result<(), PropagationError> {
    for (from_idx, deps) in edges.iter().enumerate() {
        let from = from_idx as u32;
        for &to in deps {
            if to >= from {
                return Err(PropagationError::TopologicalOrderViolation { from, to });
            }
        }
    }
    Ok(())
}
