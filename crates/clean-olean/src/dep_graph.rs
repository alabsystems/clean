// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured dependency graph for Mathlib-scale .olean module loading.
//!
//! Provides [`DependencyGraph`] which parses imports from all .olean files,
//! builds an adjacency graph, runs topological sort via Kahn's algorithm,
//! detects cycles, tracks missing dependencies, and computes module depths.
//!
//! Designed for 7,000+ module graphs (Mathlib scale).

use crate::parse_imports_only;
pub use crate::verify_batch::module_name_from_path;
use hashbrown::{HashMap, HashSet};
use serde::Serialize;
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use tracing::{info, warn};

/// Structured dependency graph with topological ordering and statistics.
///
/// Build via [`DependencyGraph::build`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DependencyGraph {
    /// Module name -> node, for all successfully parsed modules.
    pub modules: HashMap<String, ModuleNode>,
    /// Module names in topological order (dependencies before dependents).
    /// Cycle modules are appended at the end.
    pub topo_order: Vec<String>,
    /// Aggregate graph statistics.
    pub stats: GraphStats,
}

/// A node in the module dependency graph.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ModuleNode {
    /// Path to the .olean file on disk.
    pub path: PathBuf,
    /// Dot-separated module name.
    pub module_name: String,
    /// Direct import names (may include names not present in the graph).
    pub imports: Vec<String>,
    /// Depth: longest path from any root (module with zero in-graph imports).
    /// Roots have depth 0.
    pub depth: usize,
}

/// Aggregate statistics about the dependency graph.
#[derive(Debug, Clone, Default, Serialize)]
#[non_exhaustive]
pub struct GraphStats {
    /// Number of modules successfully parsed and included.
    pub total_modules: usize,
    /// Number of dependency edges (only counting edges within the graph).
    pub total_edges: usize,
    /// Maximum depth across all modules.
    pub max_depth: usize,
    /// Modules involved in dependency cycles (not reachable by topo sort).
    pub cycle_modules: Vec<String>,
    /// (module_that_needs_it, missing_dep_name) for imports referencing
    /// modules not present in the discovered file set.
    pub missing_deps: Vec<(String, String)>,
    /// Files that could not be read or whose imports could not be parsed.
    pub parse_failures: Vec<(PathBuf, String)>,
}

impl DependencyGraph {
    pub fn build(olean_files: &[PathBuf], root: &Path) -> Self {
        info!(
            files = olean_files.len(),
            root = %root.display(),
            "building dependency graph"
        );

        let (mut modules, parse_failures) = parse_modules(olean_files, root);
        let mut stats = GraphStats {
            total_modules: modules.len(),
            parse_failures,
            ..GraphStats::default()
        };

        let known: HashSet<String> = modules.keys().cloned().collect();
        let mut in_degree: HashMap<String, usize> =
            modules.keys().cloned().map(|name| (name, 0usize)).collect();
        let mut dependents: HashMap<String, Vec<String>> = HashMap::new();

        for (name, node) in &modules {
            for import in &node.imports {
                if known.contains(import) {
                    stats.total_edges += 1;
                    if let Some(degree) = in_degree.get_mut(name.as_str()) {
                        *degree += 1;
                    }
                    dependents
                        .entry(import.clone())
                        .or_default()
                        .push(name.clone());
                } else {
                    stats.missing_deps.push((name.clone(), import.clone()));
                }
            }
        }

        for next in dependents.values_mut() {
            next.sort_unstable();
        }
        stats.missing_deps.sort_unstable();
        stats.parse_failures.sort_unstable();

        let (topo_order, roots, cycle_modules) = topo_sort(&in_degree, &dependents, &modules);
        if !cycle_modules.is_empty() {
            warn!(count = cycle_modules.len(), "modules in dependency cycles");
        }
        if !stats.missing_deps.is_empty() {
            warn!(
                count = stats.missing_deps.len(),
                "modules with missing dependencies"
            );
        }
        if !stats.parse_failures.is_empty() {
            warn!(
                count = stats.parse_failures.len(),
                "failed to read or parse imports"
            );
        }

        stats.max_depth = compute_depths(&mut modules, &roots, &dependents);
        stats.cycle_modules = cycle_modules;

        info!(
            modules = stats.total_modules,
            edges = stats.total_edges,
            max_depth = stats.max_depth,
            cycles = stats.cycle_modules.len(),
            missing = stats.missing_deps.len(),
            parse_failures = stats.parse_failures.len(),
            "dependency graph built"
        );

        Self {
            modules,
            topo_order,
            stats,
        }
    }

    /// Iterate over modules in topological order, yielding `&ModuleNode`.
    pub fn walk_topo_order(&self) -> impl Iterator<Item = &ModuleNode> + '_ {
        self.topo_order
            .iter()
            .filter_map(|name| self.modules.get(name.as_str()))
    }

    /// Return the number of modules in the graph.
    pub fn len(&self) -> usize {
        self.modules.len()
    }

    /// Return true if the graph is empty.
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }

    /// Return true if any dependency cycles were detected.
    pub fn has_cycles(&self) -> bool {
        !self.stats.cycle_modules.is_empty()
    }

    /// Get a module node by name.
    pub fn get(&self, module_name: &str) -> Option<&ModuleNode> {
        self.modules.get(module_name)
    }
}

fn parse_modules(
    olean_files: &[PathBuf],
    root: &Path,
) -> (HashMap<String, ModuleNode>, Vec<(PathBuf, String)>) {
    let mut modules = HashMap::with_capacity(olean_files.len());
    let mut parse_failures = Vec::new();

    for path in olean_files {
        let module_name = module_name_from_path(path, root);
        match std::fs::read(path) {
            Ok(bytes) => match parse_imports_only(&bytes) {
                Ok(imports) => {
                    let node = ModuleNode {
                        path: path.clone(),
                        module_name: module_name.clone(),
                        imports: imports
                            .into_iter()
                            .map(|import| import.module_name)
                            .collect(),
                        depth: 0,
                    };
                    if let Some(previous) = modules.insert(module_name.clone(), node) {
                        warn!(
                            module = %module_name,
                            previous = %previous.path.display(),
                            replacement = %path.display(),
                            "duplicate module name in file set; keeping last entry"
                        );
                    }
                }
                Err(err) => parse_failures.push((path.clone(), format!("import parse: {err}"))),
            },
            Err(err) => parse_failures.push((path.clone(), format!("read: {err}"))),
        }
    }

    (modules, parse_failures)
}

fn topo_sort(
    in_degree: &HashMap<String, usize>,
    dependents: &HashMap<String, Vec<String>>,
    modules: &HashMap<String, ModuleNode>,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut in_degree = in_degree.clone();
    let mut roots: Vec<String> = in_degree
        .iter()
        .filter(|(_, degree)| **degree == 0)
        .map(|(name, _)| name.clone())
        .collect();
    roots.sort_unstable();

    let mut queue: VecDeque<String> = roots.iter().cloned().collect();
    let mut ordered = Vec::with_capacity(modules.len());
    let mut visited = HashSet::with_capacity(modules.len());

    while let Some(name) = queue.pop_front() {
        if !visited.insert(name.clone()) {
            continue;
        }
        ordered.push(name.clone());
        if let Some(next) = dependents.get(name.as_str()) {
            let mut ready = Vec::new();
            for dependent in next {
                if let Some(degree) = in_degree.get_mut(dependent.as_str()) {
                    *degree = degree.saturating_sub(1);
                    if *degree == 0 {
                        ready.push(dependent.clone());
                    }
                }
            }
            ready.sort_unstable();
            queue.extend(ready);
        }
    }

    let ordered_set: HashSet<String> = ordered.iter().cloned().collect();
    let mut cycle_modules: Vec<String> = modules
        .keys()
        .filter(|name| !ordered_set.contains(name.as_str()))
        .cloned()
        .collect();
    cycle_modules.sort_unstable();
    ordered.extend(cycle_modules.iter().cloned());

    (ordered, roots, cycle_modules)
}

fn compute_depths(
    modules: &mut HashMap<String, ModuleNode>,
    roots: &[String],
    dependents: &HashMap<String, Vec<String>>,
) -> usize {
    let pending: HashMap<String, usize> = modules
        .iter()
        .map(|(name, node)| {
            let count = node
                .imports
                .iter()
                .filter(|import| modules.contains_key(import.as_str()))
                .count();
            (name.clone(), count)
        })
        .collect();
    let mut pending = pending;

    let mut depths = HashMap::with_capacity(modules.len());
    let mut queue = VecDeque::new();
    for root in roots {
        depths.insert(root.clone(), 0usize);
        queue.push_back(root.clone());
    }

    while let Some(name) = queue.pop_front() {
        let current_depth = depths.get(name.as_str()).copied().unwrap_or(0);
        if let Some(next) = dependents.get(name.as_str()) {
            for dependent in next {
                let next_depth = current_depth.saturating_add(1);
                match depths.get_mut(dependent.as_str()) {
                    Some(depth) if *depth < next_depth => *depth = next_depth,
                    None => {
                        depths.insert(dependent.clone(), next_depth);
                    }
                    _ => {}
                }
                if let Some(remaining) = pending.get_mut(dependent.as_str()) {
                    *remaining = remaining.saturating_sub(1);
                    if *remaining == 0 {
                        queue.push_back(dependent.clone());
                    }
                }
            }
        }
    }

    let mut max_depth = 0usize;
    for (name, node) in modules.iter_mut() {
        let depth = depths.get(name.as_str()).copied().unwrap_or(0);
        node.depth = depth;
        max_depth = max_depth.max(depth);
    }
    max_depth
}

// -- Tests --------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_node(name: &str, imports: &[&str]) -> (String, ModuleNode) {
        (
            name.to_string(),
            ModuleNode {
                path: PathBuf::from(format!("{name}.olean")),
                module_name: name.to_string(),
                imports: imports.iter().map(|s| s.to_string()).collect(),
                depth: 0,
            },
        )
    }

    fn build_test_graph(
        nodes: Vec<(String, ModuleNode)>,
    ) -> (
        HashMap<String, usize>,
        HashMap<String, Vec<String>>,
        HashMap<String, ModuleNode>,
    ) {
        let modules: HashMap<String, ModuleNode> = nodes.into_iter().collect();
        let known: HashSet<String> = modules.keys().cloned().collect();
        let mut in_degree: HashMap<String, usize> =
            modules.keys().cloned().map(|n| (n, 0)).collect();
        let mut dependents: HashMap<String, Vec<String>> = HashMap::new();

        for (name, node) in &modules {
            for imp in &node.imports {
                if known.contains(imp) {
                    *in_degree.get_mut(name.as_str()).expect("in_degree entry") += 1;
                    dependents
                        .entry(imp.clone())
                        .or_default()
                        .push(name.clone());
                }
            }
        }
        for v in dependents.values_mut() {
            v.sort_unstable();
        }

        (in_degree, dependents, modules)
    }

    #[test]
    fn test_topo_sort_simple_chain() {
        let (in_deg, deps, modules) = build_test_graph(vec![
            make_node("C", &[]),
            make_node("B", &["C"]),
            make_node("A", &["B"]),
        ]);
        let (ordered, _roots, cycles) = topo_sort(&in_deg, &deps, &modules);

        assert!(cycles.is_empty(), "no cycles expected");
        assert_eq!(ordered.len(), 3);

        let pos = |name: &str| ordered.iter().position(|n| n == name).expect(name);
        assert!(pos("C") < pos("B"), "C before B");
        assert!(pos("B") < pos("A"), "B before A");
    }

    #[test]
    fn test_topo_sort_with_cycle() {
        let (in_deg, deps, modules) =
            build_test_graph(vec![make_node("A", &["B"]), make_node("B", &["A"])]);
        let (ordered, _roots, cycles) = topo_sort(&in_deg, &deps, &modules);

        assert_eq!(cycles.len(), 2, "both modules in cycle");
        assert_eq!(ordered.len(), 2, "all modules still in output");
    }

    #[test]
    fn test_topo_sort_missing_dep_ignored() {
        let (in_deg, deps, modules) = build_test_graph(vec![make_node("A", &["External"])]);
        let (ordered, _roots, cycles) = topo_sort(&in_deg, &deps, &modules);

        assert!(cycles.is_empty(), "no cycles");
        assert_eq!(ordered, vec!["A"]);
    }

    #[test]
    fn test_compute_depths_chain() {
        let (in_deg, deps, mut modules) = build_test_graph(vec![
            make_node("C", &[]),
            make_node("B", &["C"]),
            make_node("A", &["B"]),
        ]);
        let (_ordered, roots, _cycles) = topo_sort(&in_deg, &deps, &modules);
        let max_d = compute_depths(&mut modules, &roots, &deps);

        assert_eq!(modules.get("C").expect("C").depth, 0);
        assert_eq!(modules.get("B").expect("B").depth, 1);
        assert_eq!(modules.get("A").expect("A").depth, 2);
        assert_eq!(max_d, 2);
    }

    #[test]
    fn test_compute_depths_diamond() {
        let (in_deg, deps, mut modules) = build_test_graph(vec![
            make_node("A", &[]),
            make_node("B", &["A"]),
            make_node("C", &["A"]),
            make_node("D", &["B", "C"]),
        ]);
        let (_ordered, roots, _cycles) = topo_sort(&in_deg, &deps, &modules);
        let max_d = compute_depths(&mut modules, &roots, &deps);

        assert_eq!(modules.get("A").expect("A").depth, 0);
        assert_eq!(modules.get("B").expect("B").depth, 1);
        assert_eq!(modules.get("C").expect("C").depth, 1);
        assert_eq!(modules.get("D").expect("D").depth, 2);
        assert_eq!(max_d, 2);
    }

    #[test]
    fn test_empty_graph() {
        let modules: HashMap<String, ModuleNode> = HashMap::new();
        let in_deg: HashMap<String, usize> = HashMap::new();
        let deps: HashMap<String, Vec<String>> = HashMap::new();
        let (ordered, roots, cycles) = topo_sort(&in_deg, &deps, &modules);

        assert!(ordered.is_empty());
        assert!(roots.is_empty());
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_graph_stats_serializable() {
        let stats = GraphStats {
            total_modules: 100,
            total_edges: 500,
            max_depth: 15,
            cycle_modules: vec![],
            missing_deps: vec![("A".into(), "Init".into())],
            parse_failures: vec![],
        };
        let json = serde_json::to_string(&stats).expect("should serialize");
        assert!(json.contains("\"total_modules\":100"));
        assert!(json.contains("\"max_depth\":15"));
    }

    #[test]
    fn test_topo_sort_wide_fan_out() {
        // Root with 5 leaf dependents
        let mut nodes = vec![make_node("Root", &[])];
        for i in 0..5 {
            nodes.push(make_node(&format!("Leaf{i}"), &["Root"]));
        }
        let (in_deg, deps, modules) = build_test_graph(nodes);
        let (ordered, roots, cycles) = topo_sort(&in_deg, &deps, &modules);

        assert!(cycles.is_empty());
        assert_eq!(roots, vec!["Root"]);
        assert_eq!(ordered[0], "Root");
        assert_eq!(ordered.len(), 6);
    }
}
