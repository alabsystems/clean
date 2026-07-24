// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended coercion analysis: chain optimization, conflict detection, cost
//! model, statistics, graph visualization, type compatibility matrix, and
//! coercion validation.
//!
//! Builds on [`crate::coercion`] and [`crate::coercion_ext`] with analytic
//! capabilities for introspecting and optimizing the coercion graph.
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Meta/Coe.lean`

use std::collections::{HashMap, HashSet, VecDeque};

use clean_kernel::name::Name;

use crate::coercion::{CoercionEntry, CoercionKind, CoercionPath, CoercionRegistry};

/// Errors from coercion analysis operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum CoercionAnalysisError {
    #[error("coercion cycle detected: {path}")]
    CycleDetected { path: String },
    #[error("ambiguous coercion from '{from_type}' to '{to_type}': {count} paths with equal cost")]
    AmbiguousCoercion {
        from_type: String,
        to_type: String,
        count: usize,
    },
    #[error("no coercion path from '{from_type}' to '{to_type}'")]
    NoPath { from_type: String, to_type: String },
    #[error("registering coercion from '{from_type}' to '{to_type}' would create a cycle")]
    WouldCreateCycle { from_type: String, to_type: String },
}

/// Cost assigned to a single coercion step. Lower is preferred.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct CoercionCost(u32);

impl CoercionCost {
    pub(crate) const ZERO: Self = Self(0);
    #[must_use]
    pub(crate) fn new(cost: u32) -> Self {
        Self(cost)
    }
    #[must_use]
    pub(crate) fn value(self) -> u32 {
        self.0
    }
    #[must_use]
    pub(crate) fn saturating_add(self, other: Self) -> Self {
        Self(self.0.saturating_add(other.0))
    }
}

/// Default cost assignments per coercion kind.
#[must_use]
pub(crate) fn default_cost(kind: &CoercionKind) -> CoercionCost {
    match kind {
        CoercionKind::BuiltinUpcast => CoercionCost::new(1),
        CoercionKind::Direct => CoercionCost::new(2),
        CoercionKind::CoeTC => CoercionCost::new(3),
        CoercionKind::CoeHTCoe => CoercionCost::new(4),
    }
}

/// Compute the total cost of a coercion path using the default cost model.
#[must_use]
pub(crate) fn path_cost(path: &CoercionPath) -> CoercionCost {
    path_cost_with(path, default_cost)
}

/// Compute the total cost of a coercion path with a custom cost function.
#[must_use]
pub(crate) fn path_cost_with(
    path: &CoercionPath,
    cost_fn: impl Fn(&CoercionKind) -> CoercionCost,
) -> CoercionCost {
    path.steps.iter().fold(CoercionCost::ZERO, |acc, entry| {
        acc.saturating_add(cost_fn(&entry.kind))
    })
}

/// Aggregated statistics about the coercion graph.
#[derive(Debug, Clone, Default)]
pub(crate) struct CoercionStats {
    pub(crate) total_coercions: usize,
    pub(crate) by_kind: HashMap<CoercionKind, usize>,
    pub(crate) source_types: usize,
    pub(crate) target_types: usize,
    pub(crate) max_out_degree: usize,
    pub(crate) max_out_degree_type: Option<Name>,
    pub(crate) bidirectional_types: usize,
}

/// Compute statistics for a coercion registry.
#[must_use]
pub(crate) fn compute_stats(registry: &CoercionRegistry) -> CoercionStats {
    let mut by_kind: HashMap<CoercionKind, usize> = HashMap::new();
    let mut sources: HashSet<Name> = HashSet::new();
    let mut targets: HashSet<Name> = HashSet::new();
    let mut out_degree: HashMap<Name, usize> = HashMap::new();
    for entry in registry.iter() {
        *by_kind.entry(entry.kind.clone()).or_default() += 1;
        sources.insert(entry.source.clone());
        targets.insert(entry.target.clone());
        *out_degree.entry(entry.source.clone()).or_default() += 1;
    }
    let (max_out_degree, max_out_degree_type) = out_degree
        .iter()
        .max_by_key(|(_, &v)| v)
        .map(|(k, &v)| (v, Some(k.clone())))
        .unwrap_or((0, None));
    CoercionStats {
        total_coercions: registry.len(),
        by_kind,
        source_types: sources.len(),
        target_types: targets.len(),
        max_out_degree,
        max_out_degree_type,
        bidirectional_types: sources.intersection(&targets).count(),
    }
}

/// A detected conflict: multiple coercion paths between two types.
#[derive(Debug, Clone)]
pub(crate) struct CoercionConflict {
    pub(crate) source: Name,
    pub(crate) target: Name,
    pub(crate) paths: Vec<CoercionPath>,
    /// Whether costs are equal (true ambiguity) or differ (resolvable).
    pub(crate) is_true_ambiguity: bool,
}

/// Maximum BFS depth for path enumeration.
const MAX_SEARCH_DEPTH: usize = 6;

/// Find all conflicting (ambiguous) coercion paths in the registry.
#[must_use]
pub(crate) fn detect_conflicts(registry: &CoercionRegistry) -> Vec<CoercionConflict> {
    let mut conflicts = Vec::new();
    let mut checked: HashSet<(Name, Name)> = HashSet::new();
    let mut all_types: HashSet<Name> = HashSet::new();
    for entry in registry.iter() {
        all_types.insert(entry.source.clone());
        all_types.insert(entry.target.clone());
    }
    let types_vec: Vec<Name> = all_types.into_iter().collect();
    for source in &types_vec {
        for target in &types_vec {
            if source == target {
                continue;
            }
            let key = (source.clone(), target.clone());
            if checked.contains(&key) {
                continue;
            }
            checked.insert(key);
            let paths = find_all_paths_bfs(registry, source, target, MAX_SEARCH_DEPTH);
            if paths.len() > 1 {
                let costs: Vec<CoercionCost> = paths.iter().map(path_cost).collect();
                let is_true_ambiguity = costs.windows(2).all(|w| w[0] == w[1]);
                conflicts.push(CoercionConflict {
                    source: source.clone(),
                    target: target.clone(),
                    paths,
                    is_true_ambiguity,
                });
            }
        }
    }
    conflicts
}

/// BFS collecting all paths from `source` to `target` up to `max_depth`.
fn find_all_paths_bfs(
    registry: &CoercionRegistry,
    source: &Name,
    target: &Name,
    max_depth: usize,
) -> Vec<CoercionPath> {
    let mut result = Vec::new();
    let mut queue: VecDeque<(Name, Vec<CoercionEntry>, HashSet<Name>)> = VecDeque::new();
    let mut init_visited = HashSet::new();
    init_visited.insert(source.clone());
    queue.push_back((source.clone(), Vec::new(), init_visited));
    while let Some((current, path, visited)) = queue.pop_front() {
        if path.len() >= max_depth {
            continue;
        }
        for entry in registry.iter() {
            if entry.source != current {
                continue;
            }
            let mut new_path = path.clone();
            new_path.push(entry.clone());
            if entry.target == *target {
                result.push(CoercionPath { steps: new_path });
                continue;
            }
            if !visited.contains(&entry.target) {
                let mut new_visited = visited.clone();
                new_visited.insert(entry.target.clone());
                queue.push_back((entry.target.clone(), new_path, new_visited));
            }
        }
    }
    result
}

/// Find the minimum-cost coercion path from `source` to `target`.
///
/// Returns `Err` if no path exists or multiple paths have identical minimum
/// cost (true ambiguity).
pub(crate) fn find_optimal_path(
    registry: &CoercionRegistry,
    source: &Name,
    target: &Name,
) -> Result<CoercionPath, CoercionAnalysisError> {
    find_optimal_path_with(registry, source, target, default_cost)
}

/// Find the minimum-cost path with a custom cost function.
pub(crate) fn find_optimal_path_with(
    registry: &CoercionRegistry,
    source: &Name,
    target: &Name,
    cost_fn: impl Fn(&CoercionKind) -> CoercionCost,
) -> Result<CoercionPath, CoercionAnalysisError> {
    let paths = find_all_paths_bfs(registry, source, target, MAX_SEARCH_DEPTH);
    if paths.is_empty() {
        return Err(CoercionAnalysisError::NoPath {
            from_type: source.to_string(),
            to_type: target.to_string(),
        });
    }
    let mut costed: Vec<(CoercionCost, CoercionPath)> = paths
        .into_iter()
        .map(|p| {
            let c = path_cost_with(&p, &cost_fn);
            (c, p)
        })
        .collect();
    costed.sort_by_key(|(c, _)| *c);
    if costed.len() > 1 && costed[0].0 == costed[1].0 {
        let count = costed.iter().filter(|(c, _)| *c == costed[0].0).count();
        return Err(CoercionAnalysisError::AmbiguousCoercion {
            from_type: source.to_string(),
            to_type: target.to_string(),
            count,
        });
    }
    Ok(costed
        .into_iter()
        .next()
        .expect("invariant: non-empty costed vec")
        .1)
}

/// Detect cycles in the coercion graph via DFS.
///
/// Returns a list of cycle descriptions. An empty list means no cycles.
#[must_use]
pub(crate) fn detect_cycles(registry: &CoercionRegistry) -> Vec<String> {
    let mut adjacency: HashMap<Name, Vec<Name>> = HashMap::new();
    for entry in registry.iter() {
        adjacency
            .entry(entry.source.clone())
            .or_default()
            .push(entry.target.clone());
    }
    let all_nodes: HashSet<Name> = adjacency
        .keys()
        .chain(adjacency.values().flat_map(|v| v.iter()))
        .cloned()
        .collect();
    let mut visited: HashSet<Name> = HashSet::new();
    let mut on_stack: HashSet<Name> = HashSet::new();
    let mut cycles = Vec::new();
    for node in &all_nodes {
        if !visited.contains(node) {
            dfs_cycle_check(
                node,
                &adjacency,
                &mut visited,
                &mut on_stack,
                &mut Vec::new(),
                &mut cycles,
            );
        }
    }
    cycles
}

fn dfs_cycle_check(
    node: &Name,
    adjacency: &HashMap<Name, Vec<Name>>,
    visited: &mut HashSet<Name>,
    on_stack: &mut HashSet<Name>,
    path: &mut Vec<Name>,
    cycles: &mut Vec<String>,
) {
    visited.insert(node.clone());
    on_stack.insert(node.clone());
    path.push(node.clone());
    if let Some(neighbors) = adjacency.get(node) {
        for neighbor in neighbors {
            if on_stack.contains(neighbor) {
                let cycle_start = path.iter().position(|n| n == neighbor).unwrap_or(0);
                let names: Vec<String> =
                    path[cycle_start..].iter().map(|n| n.to_string()).collect();
                cycles.push(format!("{} -> {}", names.join(" -> "), neighbor));
            } else if !visited.contains(neighbor) {
                dfs_cycle_check(neighbor, adjacency, visited, on_stack, path, cycles);
            }
        }
    }
    path.pop();
    on_stack.remove(node);
}

/// Check whether adding a coercion would create a cycle.
pub(crate) fn validate_no_cycle(
    registry: &CoercionRegistry,
    source: &Name,
    target: &Name,
) -> Result<(), CoercionAnalysisError> {
    let paths = find_all_paths_bfs(registry, target, source, MAX_SEARCH_DEPTH);
    if paths.is_empty() {
        Ok(())
    } else {
        Err(CoercionAnalysisError::WouldCreateCycle {
            from_type: source.to_string(),
            to_type: target.to_string(),
        })
    }
}

/// Generate a DOT format representation of the coercion graph.
#[must_use]
pub(crate) fn to_dot(registry: &CoercionRegistry) -> String {
    let mut out = String::from("digraph coercions {\n  rankdir=LR;\n  node [shape=box];\n");
    let mut edges: Vec<&CoercionEntry> = registry.iter().collect();
    edges.sort_by(|a, b| {
        (a.source.to_string(), a.target.to_string())
            .cmp(&(b.source.to_string(), b.target.to_string()))
    });
    for entry in &edges {
        let color = match entry.kind {
            CoercionKind::Direct => "black",
            CoercionKind::CoeTC => "blue",
            CoercionKind::CoeHTCoe => "purple",
            CoercionKind::BuiltinUpcast => "green",
        };
        out.push_str(&format!(
            "  \"{}\" -> \"{}\" [label=\"{}\" color={}];\n",
            entry.source, entry.target, entry.fn_name, color,
        ));
    }
    out.push_str("}\n");
    out
}

/// Entry in the compatibility matrix: the minimum cost to coerce between types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Compatibility {
    Same,
    Coercible(CoercionCost),
    Incompatible,
}

/// A compatibility matrix between a set of types.
#[derive(Debug, Clone)]
pub(crate) struct CompatibilityMatrix {
    pub(crate) types: Vec<Name>,
    matrix: Vec<Compatibility>,
}

impl CompatibilityMatrix {
    #[must_use]
    pub(crate) fn get(&self, source: &Name, target: &Name) -> Compatibility {
        let row = self.types.iter().position(|n| n == source);
        let col = self.types.iter().position(|n| n == target);
        match (row, col) {
            (Some(r), Some(c)) => self.matrix[r * self.types.len() + c],
            _ => Compatibility::Incompatible,
        }
    }
    #[must_use]
    pub(crate) fn type_count(&self) -> usize {
        self.types.len()
    }
    #[must_use]
    pub(crate) fn coercible_count(&self) -> usize {
        self.matrix
            .iter()
            .filter(|c| matches!(c, Compatibility::Coercible(_)))
            .count()
    }
}

/// Build a compatibility matrix for the given type names (empty = auto-collect).
#[must_use]
pub(crate) fn build_compatibility_matrix(
    registry: &CoercionRegistry,
    types: &[Name],
) -> CompatibilityMatrix {
    let type_list: Vec<Name> = if types.is_empty() {
        let mut all: HashSet<Name> = HashSet::new();
        for entry in registry.iter() {
            all.insert(entry.source.clone());
            all.insert(entry.target.clone());
        }
        let mut sorted: Vec<Name> = all.into_iter().collect();
        sorted.sort_by_key(|a| a.to_string());
        sorted
    } else {
        types.to_vec()
    };
    let n = type_list.len();
    let mut matrix = vec![Compatibility::Incompatible; n * n];
    for (i, src) in type_list.iter().enumerate() {
        for (j, tgt) in type_list.iter().enumerate() {
            if i == j {
                matrix[i * n + j] = Compatibility::Same;
                continue;
            }
            let paths = find_all_paths_bfs(registry, src, tgt, MAX_SEARCH_DEPTH);
            if let Some(min_cost) = paths.iter().map(path_cost).min() {
                matrix[i * n + j] = Compatibility::Coercible(min_cost);
            }
        }
    }
    CompatibilityMatrix {
        types: type_list,
        matrix,
    }
}

/// Result of running all validation checks on a coercion registry.
#[derive(Debug, Clone)]
pub(crate) struct ValidationResult {
    pub(crate) cycles: Vec<String>,
    pub(crate) conflicts: Vec<CoercionConflict>,
    pub(crate) stats: CoercionStats,
}

impl ValidationResult {
    #[must_use]
    pub(crate) fn is_valid(&self) -> bool {
        self.cycles.is_empty() && self.conflicts.iter().all(|c| !c.is_true_ambiguity)
    }
    #[must_use]
    pub(crate) fn true_ambiguity_count(&self) -> usize {
        self.conflicts
            .iter()
            .filter(|c| c.is_true_ambiguity)
            .count()
    }
}

/// Run all validation checks on a coercion registry.
#[must_use]
pub(crate) fn validate(registry: &CoercionRegistry) -> ValidationResult {
    ValidationResult {
        cycles: detect_cycles(registry),
        conflicts: detect_conflicts(registry),
        stats: compute_stats(registry),
    }
}

#[cfg(test)]
#[path = "coercion_ext2_tests.rs"]
mod tests;
