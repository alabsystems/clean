// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended dependency graph analysis (phase 2): transitive closure,
//! critical path, parallelism estimation, and layered scheduling.
//!
//! Graph metrics, subgraph extraction, and impact analysis are in
//! [`super::dep_graph_ext2_impact`].
//!
//! Builds on [`super::dep_graph_ext::ExtDepGraph`] and [`super::dep_graph_ext::DepNode`].

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use super::dep_graph_ext::{DepNode, ExtDepGraph};

// ─────────────────────────────────────────────────────────────────────────────
// Error type
// ─────────────────────────────────────────────────────────────────────────────

/// Errors produced by extended graph analysis operations.
#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum DepGraphExt2Error {
    /// The graph contains a cycle, which prevents the requested analysis.
    #[error("graph contains a cycle through: {0:?}")]
    CycleDetected(Vec<DepNode>),

    /// A requested node does not exist in the graph.
    #[error("node not found in graph: {0:?}")]
    NodeNotFound(DepNode),

    /// Depth limit exceeded during transitive traversal.
    #[error("depth limit ({0}) exceeded during traversal")]
    DepthLimitExceeded(usize),
}

// ─────────────────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────────────────

/// Configuration for ext2 analysis operations.
#[derive(Debug, Clone)]
pub(crate) struct Ext2Config {
    /// Maximum traversal depth for transitive operations.
    pub(crate) max_depth: usize,
}

impl Default for Ext2Config {
    fn default() -> Self {
        Self { max_depth: 10_000 }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Result types
// ─────────────────────────────────────────────────────────────────────────────

/// A single layer in a layered schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScheduleLayer {
    /// Layer index (0 = leaves / no dependencies).
    pub(crate) depth: usize,
    /// Nodes assignable to this layer (executable in parallel).
    pub(crate) nodes: Vec<DepNode>,
}

/// Result of critical path analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CriticalPath {
    /// Ordered sequence of nodes on the longest dependency chain.
    pub(crate) path: Vec<DepNode>,
    /// Length of the critical path (number of edges, i.e., `path.len() - 1`).
    pub(crate) length: usize,
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitive closure
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Compute the full transitive dependency set for `start`.
    ///
    /// Returns all nodes reachable via forward edges (dependencies).
    /// Does NOT include `start` itself.
    pub(crate) fn transitive_closure(
        &self,
        start: &DepNode,
        config: &Ext2Config,
    ) -> Result<BTreeSet<DepNode>, DepGraphExt2Error> {
        if !self.forward.contains_key(start) && !self.reverse.contains_key(start) {
            return Err(DepGraphExt2Error::NodeNotFound(start.clone()));
        }
        let mut visited = BTreeSet::new();
        let mut queue: VecDeque<(DepNode, usize)> = VecDeque::new();
        for dep in self.deps_of(start) {
            queue.push_back((dep, 1));
        }
        while let Some((node, depth)) = queue.pop_front() {
            if depth > config.max_depth {
                return Err(DepGraphExt2Error::DepthLimitExceeded(config.max_depth));
            }
            if !visited.insert(node.clone()) {
                continue;
            }
            for dep in self.deps_of(&node) {
                if !visited.contains(&dep) {
                    queue.push_back((dep, depth + 1));
                }
            }
        }
        Ok(visited)
    }

    /// Compute full transitive reverse-dependency set for `start`.
    ///
    /// Returns all nodes that transitively depend on `start` (the impact set).
    /// Does NOT include `start` itself.
    pub(crate) fn transitive_dependents(
        &self,
        start: &DepNode,
        config: &Ext2Config,
    ) -> Result<BTreeSet<DepNode>, DepGraphExt2Error> {
        if !self.forward.contains_key(start) && !self.reverse.contains_key(start) {
            return Err(DepGraphExt2Error::NodeNotFound(start.clone()));
        }
        let mut visited = BTreeSet::new();
        let mut queue: VecDeque<(DepNode, usize)> = VecDeque::new();
        for dep in self.dependents_of(start) {
            queue.push_back((dep, 1));
        }
        while let Some((node, depth)) = queue.pop_front() {
            if depth > config.max_depth {
                return Err(DepGraphExt2Error::DepthLimitExceeded(config.max_depth));
            }
            if !visited.insert(node.clone()) {
                continue;
            }
            for dep in self.dependents_of(&node) {
                if !visited.contains(&dep) {
                    queue.push_back((dep, depth + 1));
                }
            }
        }
        Ok(visited)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Critical path analysis
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Find the longest dependency chain in a DAG.
    ///
    /// Returns the critical path (nodes in order from root to leaf of the
    /// longest chain). Returns `Err` if the graph contains a cycle.
    pub(crate) fn critical_path(&self) -> Result<CriticalPath, DepGraphExt2Error> {
        let topo = self.topological_order()?;
        if topo.is_empty() {
            return Ok(CriticalPath {
                path: Vec::new(),
                length: 0,
            });
        }

        // longest-path DP on the topological order
        let mut dist: HashMap<&DepNode, usize> = HashMap::new();
        let mut pred: HashMap<&DepNode, &DepNode> = HashMap::new();

        for node in &topo {
            dist.insert(node, 0);
        }

        for node in &topo {
            let d = dist[node];
            for dep in self.deps_of(node) {
                if let Some(dep_ref) = topo.iter().find(|n| **n == dep) {
                    if d + 1 > *dist.get(dep_ref).unwrap_or(&0) {
                        dist.insert(dep_ref, d + 1);
                        pred.insert(dep_ref, node);
                    }
                }
            }
        }

        // Find endpoint with maximum distance
        let (&end, &max_dist) = dist.iter().max_by_key(|(_, &d)| d).expect("non-empty topo");

        // Reconstruct path
        let mut path = vec![end.clone()];
        let mut cur = end;
        while let Some(&prev) = pred.get(cur) {
            path.push(prev.clone());
            cur = prev;
        }
        path.reverse();

        Ok(CriticalPath {
            length: max_dist,
            path,
        })
    }

    /// Topological sort of graph nodes. Returns `Err` on cycles.
    pub(crate) fn topological_order(&self) -> Result<Vec<DepNode>, DepGraphExt2Error> {
        let all = self.all_nodes();
        let n = all.len();
        if n == 0 {
            return Ok(Vec::new());
        }

        let mut in_deg: HashMap<DepNode, usize> = HashMap::with_capacity(n);
        for node in &all {
            in_deg.entry(node.clone()).or_insert(0);
            for dep in self.deps_of(node) {
                if all.contains(&dep) {
                    *in_deg.entry(dep).or_insert(0) += 1;
                }
            }
        }

        let mut queue: VecDeque<DepNode> = in_deg
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(n, _)| n.clone())
            .collect();
        let mut order = Vec::with_capacity(n);

        while let Some(node) = queue.pop_front() {
            order.push(node.clone());
            for dep in self.deps_of(&node) {
                if let Some(d) = in_deg.get_mut(&dep) {
                    *d = d.saturating_sub(1);
                    if *d == 0 {
                        queue.push_back(dep);
                    }
                }
            }
        }

        if order.len() != n {
            let cycle_node = in_deg
                .iter()
                .find(|(n, &d)| d > 0 && !order.contains(n))
                .map(|(n, _)| n.clone())
                .expect("invariant: remaining nodes exist");
            return Err(DepGraphExt2Error::CycleDetected(vec![cycle_node]));
        }
        Ok(order)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Parallelism estimation
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Estimate the maximum parallelism available in the graph.
    ///
    /// This is the width of the widest layer in a layered schedule — the
    /// maximum number of nodes whose dependencies are all satisfied that can
    /// execute simultaneously.
    ///
    /// Returns `Err` if the graph contains a cycle.
    pub(crate) fn max_parallelism(&self) -> Result<usize, DepGraphExt2Error> {
        let layers = self.layered_schedule()?;
        Ok(layers.iter().map(|l| l.nodes.len()).max().unwrap_or(0))
    }

    /// Compute the critical-path ratio: `critical_path_length / num_nodes`.
    ///
    /// Lower values indicate more parallelism potential. A value of 1.0 means
    /// the graph is a single chain; near-zero means it is very wide.
    pub(crate) fn serialization_ratio(&self) -> Result<f64, DepGraphExt2Error> {
        let n = self.all_nodes().len();
        if n == 0 {
            return Ok(0.0);
        }
        let cp = self.critical_path()?;
        Ok(cp.path.len() as f64 / n as f64)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Layered scheduling
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Assign nodes to parallel layers respecting dependencies.
    ///
    /// Layer 0 contains nodes with no dependencies. Layer N+1 contains nodes
    /// whose dependencies are all in layers <= N. Returns `Err` on cycles.
    pub(crate) fn layered_schedule(&self) -> Result<Vec<ScheduleLayer>, DepGraphExt2Error> {
        let all = self.all_nodes();
        if all.is_empty() {
            return Ok(Vec::new());
        }

        let mut in_deg: HashMap<DepNode, usize> = HashMap::with_capacity(all.len());
        for node in &all {
            in_deg.entry(node.clone()).or_insert(0);
            for dep in self.deps_of(node) {
                if all.contains(&dep) {
                    *in_deg.entry(node.clone()).or_insert(0) += 1;
                }
            }
        }

        let mut layers = Vec::new();
        let mut remaining = in_deg;

        loop {
            let ready: Vec<DepNode> = remaining
                .iter()
                .filter(|(_, &d)| d == 0)
                .map(|(n, _)| n.clone())
                .collect();

            if ready.is_empty() {
                if remaining.is_empty() {
                    break;
                }
                let cycle_node = remaining
                    .keys()
                    .next()
                    .expect("non-empty remaining")
                    .clone();
                return Err(DepGraphExt2Error::CycleDetected(vec![cycle_node]));
            }

            let layer = ScheduleLayer {
                depth: layers.len(),
                nodes: ready.clone(),
            };

            for node in &ready {
                remaining.remove(node);
            }

            for node in &ready {
                for dependent in self.dependents_of(node) {
                    if let Some(d) = remaining.get_mut(&dependent) {
                        *d = d.saturating_sub(1);
                    }
                }
            }

            layers.push(layer);
        }

        Ok(layers)
    }

    /// Compute the node-to-layer mapping for quick lookup.
    pub(crate) fn node_layer_map(&self) -> Result<BTreeMap<DepNode, usize>, DepGraphExt2Error> {
        let layers = self.layered_schedule()?;
        let mut map = BTreeMap::new();
        for layer in &layers {
            for node in &layer.nodes {
                map.insert(node.clone(), layer.depth);
            }
        }
        Ok(map)
    }
}
