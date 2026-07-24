// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Graph metrics, subgraph extraction, and impact analysis for dependency graphs.
//!
//! Companion to [`super::dep_graph_ext2`] which provides transitive closure,
//! critical path, parallelism estimation, and layered scheduling.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use super::dep_graph_ext::{DepNode, ExtDepGraph};
use super::dep_graph_ext2::{DepGraphExt2Error, Ext2Config};

// ─────────────────────────────────────────────────────────────────────────────
// Graph metrics
// ─────────────────────────────────────────────────────────────────────────────

/// Metrics describing the shape of a dependency graph.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct GraphMetrics {
    /// Number of nodes.
    pub(crate) node_count: usize,
    /// Number of directed edges.
    pub(crate) edge_count: usize,
    /// Graph density: edges / (nodes * (nodes - 1)), 0.0 for trivial graphs.
    pub(crate) density: f64,
    /// Average out-degree.
    pub(crate) avg_out_degree: f64,
    /// Maximum out-degree.
    pub(crate) max_out_degree: usize,
    /// Average clustering coefficient (fraction of a node's neighbors that are
    /// themselves connected). Computed over the undirected projection.
    pub(crate) avg_clustering_coefficient: f64,
}

impl ExtDepGraph {
    /// Compute structural metrics for the graph.
    #[must_use]
    pub(crate) fn graph_metrics(&self) -> GraphMetrics {
        let all = self.all_nodes();
        let n = all.len();
        if n == 0 {
            return GraphMetrics {
                node_count: 0,
                edge_count: 0,
                density: 0.0,
                avg_out_degree: 0.0,
                max_out_degree: 0,
                avg_clustering_coefficient: 0.0,
            };
        }

        let mut edge_count: usize = 0;
        let mut out_degrees: Vec<usize> = Vec::with_capacity(n);

        for node in &all {
            let out_deg = self.deps_of(node).len();
            out_degrees.push(out_deg);
            edge_count += out_deg;
        }

        let max_out_degree = out_degrees.iter().copied().max().unwrap_or(0);
        let avg_out_degree = edge_count as f64 / n as f64;
        let density = if n > 1 {
            edge_count as f64 / (n as f64 * (n as f64 - 1.0))
        } else {
            0.0
        };

        let avg_clustering_coefficient = avg_clustering_coeff(self, &all);

        GraphMetrics {
            node_count: n,
            edge_count,
            density,
            avg_out_degree,
            max_out_degree,
            avg_clustering_coefficient,
        }
    }
}

/// Average local clustering coefficient over all nodes (undirected projection).
fn avg_clustering_coeff(graph: &ExtDepGraph, all: &BTreeSet<DepNode>) -> f64 {
    let n = all.len();
    if n == 0 {
        return 0.0;
    }

    // Build undirected neighbor sets (two-pass to avoid double mutable borrow)
    let mut neighbors: HashMap<&DepNode, HashSet<&DepNode>> = HashMap::new();
    // Collect edges first, then insert both directions
    let mut edge_pairs: Vec<(&DepNode, &DepNode)> = Vec::new();
    for node in all {
        for dep in graph.deps_of(node) {
            if let Some(dep_ref) = all.iter().find(|n| **n == dep) {
                edge_pairs.push((node, dep_ref));
            }
        }
    }
    for &(a, b) in &edge_pairs {
        neighbors.entry(a).or_default().insert(b);
        neighbors.entry(b).or_default().insert(a);
    }

    let mut sum = 0.0;
    for node in all {
        let nbrs: Vec<&DepNode> = neighbors
            .get(node)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();
        let k = nbrs.len();
        if k < 2 {
            continue;
        }
        let mut connected = 0usize;
        for i in 0..k {
            for j in (i + 1)..k {
                if neighbors.get(nbrs[i]).is_some_and(|s| s.contains(nbrs[j])) {
                    connected += 1;
                }
            }
        }
        let possible = k * (k - 1) / 2;
        sum += connected as f64 / possible as f64;
    }

    sum / n as f64
}

// ─────────────────────────────────────────────────────────────────────────────
// Subgraph extraction
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Extract the subgraph reachable from `roots` via forward edges.
    ///
    /// The returned graph contains only nodes transitively reachable from
    /// `roots` (including `roots` themselves) and edges between those nodes.
    #[must_use]
    pub(crate) fn subgraph_from_roots(&self, roots: &[DepNode]) -> ExtDepGraph {
        let mut reachable = BTreeSet::new();
        let mut queue: VecDeque<DepNode> = roots.iter().cloned().collect();

        while let Some(node) = queue.pop_front() {
            if !reachable.insert(node.clone()) {
                continue;
            }
            for dep in self.deps_of(&node) {
                if !reachable.contains(&dep) {
                    queue.push_back(dep);
                }
            }
        }

        let mut sub = ExtDepGraph::new();
        for node in &reachable {
            sub.ensure_node(node.clone());
            for dep in self.deps_of(node) {
                if reachable.contains(&dep) {
                    sub.add_dep(node.clone(), dep);
                }
            }
        }
        sub
    }

    /// Extract the subgraph reachable from `roots` via reverse edges
    /// (upstream / "who depends on these?").
    #[must_use]
    pub(crate) fn subgraph_from_roots_reverse(&self, roots: &[DepNode]) -> ExtDepGraph {
        let mut reachable = BTreeSet::new();
        let mut queue: VecDeque<DepNode> = roots.iter().cloned().collect();

        while let Some(node) = queue.pop_front() {
            if !reachable.insert(node.clone()) {
                continue;
            }
            for dep in self.dependents_of(&node) {
                if !reachable.contains(&dep) {
                    queue.push_back(dep);
                }
            }
        }

        let mut sub = ExtDepGraph::new();
        for node in &reachable {
            sub.ensure_node(node.clone());
            for dep in self.deps_of(node) {
                if reachable.contains(&dep) {
                    sub.add_dep(node.clone(), dep);
                }
            }
        }
        sub
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Impact analysis
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Given a set of changed nodes, compute all affected downstream nodes.
    ///
    /// This is the union of transitive reverse-dependencies of every node in
    /// `changed`. The changed nodes themselves are NOT included in the result
    /// (only their dependents).
    pub(crate) fn impact_set(
        &self,
        changed: &[DepNode],
        config: &Ext2Config,
    ) -> Result<BTreeSet<DepNode>, DepGraphExt2Error> {
        let mut affected = BTreeSet::new();
        for node in changed {
            // Skip nodes not in the graph rather than erroring
            if !self.forward.contains_key(node) && !self.reverse.contains_key(node) {
                continue;
            }
            let deps = self.transitive_dependents(node, config)?;
            affected.extend(deps);
        }
        // Remove the changed nodes themselves from the result
        for node in changed {
            affected.remove(node);
        }
        Ok(affected)
    }

    /// Compute the impact score for a single node: the number of nodes that
    /// would need rechecking if it changed.
    pub(crate) fn impact_score(
        &self,
        node: &DepNode,
        config: &Ext2Config,
    ) -> Result<usize, DepGraphExt2Error> {
        let deps = self.transitive_dependents(node, config)?;
        Ok(deps.len())
    }

    /// Rank all nodes by impact score (descending). Most impactful first.
    pub(crate) fn impact_ranking(
        &self,
        config: &Ext2Config,
    ) -> Result<Vec<(DepNode, usize)>, DepGraphExt2Error> {
        let all = self.all_nodes();
        let mut ranking: Vec<(DepNode, usize)> = Vec::with_capacity(all.len());
        for node in &all {
            let score = self.impact_score(node, config)?;
            ranking.push((node.clone(), score));
        }
        ranking.sort_by_key(|b| std::cmp::Reverse(b.1));
        Ok(ranking)
    }
}
