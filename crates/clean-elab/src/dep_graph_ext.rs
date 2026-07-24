// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended dependency graph analysis for cross-module elaboration.
//!
//! Provides incremental recheck detection, parallel elaboration scheduling,
//! cycle reporting with readable error messages, import graph construction,
//! stale dependency detection, and graph serialization for caching.
//!
//! Builds on [`super::dep_graph::DependencyGraph`] which handles intra-block
//! dependency analysis. This module handles cross-module concerns.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use clean_kernel::Name;
use serde::{Deserialize, Serialize};

/// Configuration for extended dependency graph analysis.
#[derive(Debug, Clone)]
pub(crate) struct DepGraphExtConfig {
    /// Maximum depth for transitive closure computation (prevents runaway).
    pub(crate) max_transitive_depth: usize,
}

impl Default for DepGraphExtConfig {
    fn default() -> Self {
        Self {
            max_transitive_depth: 10_000,
        }
    }
}

/// A module identifier (e.g., `Init.Prelude`, `Mathlib.Topology`).
pub(crate) type ModuleId = Name;

/// Timestamp or version tag used for stale-dependency detection.
pub(crate) type VersionStamp = u64;

/// Cross-module dependency graph tracking declaration-level dependencies.
///
/// Each node is a `(module, declaration)` pair. Edges indicate that the
/// source declaration references the target declaration's definition.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct ExtDepGraph {
    /// Forward edges: node -> set of nodes it depends on.
    pub(crate) forward: BTreeMap<DepNode, BTreeSet<DepNode>>,
    /// Reverse edges: node -> set of nodes that depend on it.
    pub(crate) reverse: BTreeMap<DepNode, BTreeSet<DepNode>>,
    /// Module-level import edges: module -> set of modules it imports.
    pub(crate) module_imports: BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    /// Version stamps for stale-dependency detection.
    pub(crate) stamps: BTreeMap<DepNode, VersionStamp>,
}

/// A node in the dependency graph: a declaration within a module.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct DepNode {
    pub(crate) module: ModuleId,
    pub(crate) decl: Name,
}

impl DepNode {
    #[must_use]
    pub(crate) fn new(module: ModuleId, decl: Name) -> Self {
        Self { module, decl }
    }
}

/// A strongly connected component of declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Scc {
    pub(crate) nodes: Vec<DepNode>,
}

/// Result of parallel scheduling analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScheduleWave {
    /// Wave index (0 = no dependencies, can run first).
    pub(crate) index: usize,
    /// Nodes in this wave (can all be elaborated in parallel).
    pub(crate) nodes: Vec<DepNode>,
}

/// Dependency cycle with human-readable error message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CycleReport {
    pub(crate) cycle: Vec<DepNode>,
    pub(crate) message: String,
}

impl ExtDepGraph {
    /// Create an empty extended dependency graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a dependency edge: `from` depends on `to`.
    pub(crate) fn add_dep(&mut self, from: DepNode, to: DepNode) {
        self.forward
            .entry(from.clone())
            .or_default()
            .insert(to.clone());
        self.reverse.entry(to).or_default().insert(from);
    }

    /// Register a module import: `importer` imports `imported`.
    pub(crate) fn add_module_import(&mut self, importer: ModuleId, imported: ModuleId) {
        self.module_imports
            .entry(importer)
            .or_default()
            .insert(imported);
    }

    /// Set the version stamp for a node.
    pub(crate) fn set_stamp(&mut self, node: DepNode, stamp: VersionStamp) {
        self.stamps.insert(node, stamp);
    }

    /// Ensure a node exists in the graph (even with no edges).
    pub(crate) fn ensure_node(&mut self, node: DepNode) {
        self.forward.entry(node.clone()).or_default();
        self.reverse.entry(node).or_default();
    }

    /// Return all nodes in the graph.
    #[must_use]
    pub(crate) fn all_nodes(&self) -> BTreeSet<DepNode> {
        let mut nodes = BTreeSet::new();
        for (k, vs) in &self.forward {
            nodes.insert(k.clone());
            for v in vs {
                nodes.insert(v.clone());
            }
        }
        for (k, vs) in &self.reverse {
            nodes.insert(k.clone());
            for v in vs {
                nodes.insert(v.clone());
            }
        }
        nodes
    }

    /// Return direct dependencies of `node`.
    #[must_use]
    pub(crate) fn deps_of(&self, node: &DepNode) -> BTreeSet<DepNode> {
        self.forward.get(node).cloned().unwrap_or_default()
    }

    /// Return direct dependents (reverse deps) of `node`.
    #[must_use]
    pub(crate) fn dependents_of(&self, node: &DepNode) -> BTreeSet<DepNode> {
        self.reverse.get(node).cloned().unwrap_or_default()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Incremental recheck
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Compute which nodes need re-elaboration given a set of changed nodes.
    ///
    /// Returns the transitive closure of reverse dependencies from `changed`,
    /// including `changed` itself (the changed nodes also need rechecking).
    #[must_use]
    pub(crate) fn recheck_set(&self, changed: &[DepNode]) -> BTreeSet<DepNode> {
        let mut result = BTreeSet::new();
        let mut queue: VecDeque<DepNode> = changed.iter().cloned().collect();
        while let Some(node) = queue.pop_front() {
            if !result.insert(node.clone()) {
                continue;
            }
            for dep in self.dependents_of(&node) {
                if !result.contains(&dep) {
                    queue.push_back(dep);
                }
            }
        }
        result
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Parallel scheduling
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Compute parallel elaboration waves.
    ///
    /// Wave 0 contains nodes with no dependencies. Wave N+1 contains nodes
    /// whose dependencies are all in waves <= N. Returns `Err` with a cycle
    /// report if the graph has cycles.
    pub(crate) fn schedule_waves(&self) -> Result<Vec<ScheduleWave>, CycleReport> {
        let all_nodes = self.all_nodes();
        if all_nodes.is_empty() {
            return Ok(Vec::new());
        }

        let mut in_degree: HashMap<DepNode, usize> = HashMap::new();
        for node in &all_nodes {
            in_degree.entry(node.clone()).or_insert(0);
            for dep in self.deps_of(node) {
                if all_nodes.contains(&dep) {
                    *in_degree.entry(node.clone()).or_insert(0) += 1;
                }
            }
        }

        // Kahn's algorithm adapted for wave tracking
        let mut waves = Vec::new();
        let mut remaining = in_degree;

        loop {
            let ready: Vec<DepNode> = remaining
                .iter()
                .filter(|(_, &deg)| deg == 0)
                .map(|(n, _)| n.clone())
                .collect();

            if ready.is_empty() {
                if remaining.is_empty() {
                    break;
                }
                // Cycle detected — find one via DFS
                let start = remaining
                    .keys()
                    .next()
                    .expect("invariant: non-empty remaining");
                return Err(self.find_cycle_from(start));
            }

            let wave = ScheduleWave {
                index: waves.len(),
                nodes: ready.clone(),
            };

            for node in &ready {
                remaining.remove(node);
            }

            // Decrease in-degree for dependents of scheduled nodes
            for node in &ready {
                for dependent in self.dependents_of(node) {
                    if let Some(deg) = remaining.get_mut(&dependent) {
                        *deg = deg.saturating_sub(1);
                    }
                }
            }

            waves.push(wave);
        }

        Ok(waves)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cycle detection and reporting
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Detect all cycles in the graph, returning readable reports.
    #[must_use]
    pub(crate) fn find_cycles(&self) -> Vec<CycleReport> {
        let sccs = self.compute_sccs();
        sccs.into_iter()
            .filter(|scc| scc.nodes.len() > 1 || self.has_self_loop(&scc.nodes[0]))
            .map(|scc| {
                let names: Vec<String> = scc.nodes.iter().map(format_node).collect();
                let message = format!(
                    "Dependency cycle detected ({} declarations): {}",
                    names.len(),
                    names.join(" -> ")
                );
                CycleReport {
                    cycle: scc.nodes,
                    message,
                }
            })
            .collect()
    }

    /// Find a cycle starting from (or near) a given node via DFS.
    fn find_cycle_from(&self, start: &DepNode) -> CycleReport {
        let mut visited = HashSet::new();
        let mut path = Vec::new();
        let mut stack = vec![(start.clone(), false)];

        while let Some((node, backtrack)) = stack.pop() {
            if backtrack {
                path.pop();
                continue;
            }
            if let Some(pos) = path.iter().position(|n| n == &node) {
                let cycle: Vec<DepNode> = path[pos..].to_vec();
                let names: Vec<String> = cycle.iter().map(format_node).collect();
                return CycleReport {
                    cycle,
                    message: format!("Dependency cycle detected: {}", names.join(" -> ")),
                };
            }
            if visited.contains(&node) {
                continue;
            }
            visited.insert(node.clone());
            path.push(node.clone());
            stack.push((node.clone(), true));

            for dep in self.deps_of(&node) {
                stack.push((dep, false));
            }
        }

        // Should not reach here if called when a cycle is known to exist
        CycleReport {
            cycle: vec![start.clone()],
            message: format!("Cycle suspected near {}", format_node(start)),
        }
    }

    /// Check whether a node has an edge to itself.
    #[must_use]
    fn has_self_loop(&self, node: &DepNode) -> bool {
        self.deps_of(node).contains(node)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitive closure
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Compute the transitive closure of dependencies for a node.
    ///
    /// Returns all nodes reachable via forward edges from `start`.
    /// Respects `config.max_transitive_depth` to bound computation.
    #[must_use]
    pub(crate) fn transitive_deps(
        &self,
        start: &DepNode,
        config: &DepGraphExtConfig,
    ) -> BTreeSet<DepNode> {
        let mut result = BTreeSet::new();
        let mut queue: VecDeque<(DepNode, usize)> = VecDeque::new();
        queue.push_back((start.clone(), 0));

        while let Some((node, depth)) = queue.pop_front() {
            if depth > config.max_transitive_depth {
                continue;
            }
            if node == *start && depth > 0 {
                // Reached start again via cycle; include but don't recurse
                result.insert(node);
                continue;
            }
            if depth > 0 && !result.insert(node.clone()) {
                continue;
            }
            for dep in self.deps_of(&node) {
                if !result.contains(&dep) || dep == *start {
                    queue.push_back((dep, depth + 1));
                }
            }
        }
        result
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Strongly connected components (Tarjan's)
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Compute SCCs via iterative Tarjan's algorithm on named nodes.
    #[must_use]
    pub(crate) fn compute_sccs(&self) -> Vec<Scc> {
        let all_nodes: Vec<DepNode> = self.all_nodes().into_iter().collect();
        let n = all_nodes.len();
        let node_to_idx: HashMap<&DepNode, usize> =
            all_nodes.iter().enumerate().map(|(i, n)| (n, i)).collect();

        let mut index_counter: usize = 0;
        let mut stack: Vec<usize> = Vec::new();
        let mut on_stack = vec![false; n];
        let mut indices = vec![usize::MAX; n];
        let mut lowlinks = vec![usize::MAX; n];
        let mut result: Vec<Scc> = Vec::new();

        for v in 0..n {
            if indices[v] != usize::MAX {
                continue;
            }

            let mut dfs_stack: Vec<(usize, usize)> = vec![(v, 0)];
            indices[v] = index_counter;
            lowlinks[v] = index_counter;
            index_counter += 1;
            stack.push(v);
            on_stack[v] = true;

            while let Some(&mut (node, ref mut succ_idx)) = dfs_stack.last_mut() {
                let succs: Vec<usize> = self
                    .deps_of(&all_nodes[node])
                    .iter()
                    .filter_map(|dep| node_to_idx.get(dep).copied())
                    .collect();

                if *succ_idx < succs.len() {
                    let w = succs[*succ_idx];
                    *succ_idx += 1;

                    if indices[w] == usize::MAX {
                        indices[w] = index_counter;
                        lowlinks[w] = index_counter;
                        index_counter += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        dfs_stack.push((w, 0));
                    } else if on_stack[w] {
                        lowlinks[node] = lowlinks[node].min(indices[w]);
                    }
                } else {
                    if lowlinks[node] == indices[node] {
                        let mut scc_nodes = Vec::new();
                        while let Some(w) = stack.pop() {
                            on_stack[w] = false;
                            scc_nodes.push(all_nodes[w].clone());
                            if w == node {
                                break;
                            }
                        }
                        result.push(Scc { nodes: scc_nodes });
                    }

                    dfs_stack.pop();
                    if let Some(&mut (parent, _)) = dfs_stack.last_mut() {
                        lowlinks[parent] = lowlinks[parent].min(lowlinks[node]);
                    }
                }
            }
        }

        result
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Stale dependency detection
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Identify nodes whose dependencies have a newer stamp than themselves.
    ///
    /// A node is "stale" if any of its forward dependencies has a stamp
    /// strictly greater than the node's own stamp. Nodes without stamps
    /// are treated as having stamp 0.
    #[must_use]
    pub(crate) fn stale_nodes(&self) -> BTreeSet<DepNode> {
        let mut stale = BTreeSet::new();
        for (node, deps) in &self.forward {
            let node_stamp = self.stamps.get(node).copied().unwrap_or(0);
            for dep in deps {
                let dep_stamp = self.stamps.get(dep).copied().unwrap_or(0);
                if dep_stamp > node_stamp {
                    stale.insert(node.clone());
                    break;
                }
            }
        }
        stale
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Serialization helpers
// ─────────────────────────────────────────────────────────────────────────────

impl ExtDepGraph {
    /// Serialize the graph to JSON bytes.
    pub(crate) fn to_json(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(&SerializableExtDepGraph::from(self))
    }

    /// Deserialize a graph from JSON bytes.
    pub(crate) fn from_json(data: &[u8]) -> Result<Self, serde_json::Error> {
        serde_json::from_slice::<SerializableExtDepGraph>(data).map(Into::into)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SerializableExtDepGraph {
    forward: Vec<(DepNode, Vec<DepNode>)>,
    reverse: Vec<(DepNode, Vec<DepNode>)>,
    module_imports: Vec<(ModuleId, Vec<ModuleId>)>,
    stamps: Vec<(DepNode, VersionStamp)>,
}

impl From<&ExtDepGraph> for SerializableExtDepGraph {
    fn from(graph: &ExtDepGraph) -> Self {
        Self {
            forward: graph
                .forward
                .iter()
                .map(|(node, deps)| (node.clone(), deps.iter().cloned().collect()))
                .collect(),
            reverse: graph
                .reverse
                .iter()
                .map(|(node, dependents)| (node.clone(), dependents.iter().cloned().collect()))
                .collect(),
            module_imports: graph
                .module_imports
                .iter()
                .map(|(module, imports)| (module.clone(), imports.iter().cloned().collect()))
                .collect(),
            stamps: graph
                .stamps
                .iter()
                .map(|(node, stamp)| (node.clone(), *stamp))
                .collect(),
        }
    }
}

impl From<SerializableExtDepGraph> for ExtDepGraph {
    fn from(cache: SerializableExtDepGraph) -> Self {
        Self {
            forward: cache
                .forward
                .into_iter()
                .map(|(node, deps)| (node, deps.into_iter().collect()))
                .collect(),
            reverse: cache
                .reverse
                .into_iter()
                .map(|(node, dependents)| (node, dependents.into_iter().collect()))
                .collect(),
            module_imports: cache
                .module_imports
                .into_iter()
                .map(|(module, imports)| (module, imports.into_iter().collect()))
                .collect(),
            stamps: cache.stamps.into_iter().collect(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Format a node as `module.decl` for human-readable messages.
fn format_node(node: &DepNode) -> String {
    format!("{}.{}", node.module, node.decl)
}
