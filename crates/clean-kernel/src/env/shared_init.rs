// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared registry and dependency helpers for extracted `init_*` entrypoints.
//!
//! This module stays intentionally small and generic so extracted init families
//! can share a single representation for registration and ordering without
//! pulling in packet-specific logic.

use super::{EnvError, Environment};
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap};

/// Function pointer for a shared `Environment::init_*` entrypoint.
pub(crate) type SharedInitFn = fn(&mut Environment) -> Result<(), EnvError>;

/// Registered shared init entry.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SharedInitEntry {
    pub(crate) name: &'static str,
    pub(crate) init_fn: SharedInitFn,
}

/// Registry of extracted/shared init entrypoints.
#[derive(Clone, Debug, Default)]
pub(crate) struct SharedInitRegistry {
    entries: Vec<SharedInitEntry>,
    index: HashMap<&'static str, usize>,
}

impl SharedInitRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a shared init entrypoint by stable name.
    ///
    /// Returns `true` when the init was newly inserted and `false` when the
    /// name was already present.
    pub(crate) fn register_init(&mut self, name: &'static str, init_fn: SharedInitFn) -> bool {
        if self.index.contains_key(name) {
            return false;
        }

        let idx = self.entries.len();
        self.entries.push(SharedInitEntry { name, init_fn });
        self.index.insert(name, idx);
        true
    }

    /// Look up a previously-registered shared init entrypoint.
    pub(crate) fn get_init(&self, name: &str) -> Option<SharedInitEntry> {
        self.index
            .get(name)
            .and_then(|&idx| self.entries.get(idx))
            .copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn index_of(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }
}

pub(crate) fn register_init(
    registry: &mut SharedInitRegistry,
    name: &'static str,
    init_fn: SharedInitFn,
) -> bool {
    registry.register_init(name, init_fn)
}

pub(crate) fn get_init(registry: &SharedInitRegistry, name: &str) -> Option<SharedInitEntry> {
    registry.get_init(name)
}

/// Dependency edges between registered init entrypoints.
#[derive(Clone, Debug, Default)]
pub(crate) struct InitDependencyGraph {
    dependencies: HashMap<&'static str, BTreeSet<&'static str>>,
}

impl InitDependencyGraph {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add an init node with no dependencies.
    pub(crate) fn add_init(&mut self, name: &'static str) {
        self.dependencies.entry(name).or_default();
    }

    /// Record that `name` depends on `dependency`.
    pub(crate) fn add_dependency(&mut self, name: &'static str, dependency: &'static str) {
        self.dependencies
            .entry(name)
            .or_default()
            .insert(dependency);
    }

    fn referenced_names(&self) -> BTreeSet<&'static str> {
        let mut names = BTreeSet::new();
        for (name, deps) in &self.dependencies {
            names.insert(*name);
            names.extend(deps.iter().copied());
        }
        names
    }
}

/// Graph validation/topological sort failures for shared init entrypoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum InitGraphError {
    UnknownInits(Vec<String>),
    Cycle(Vec<String>),
}

/// Check that every graph reference resolves to a registered init and that the
/// graph is acyclic.
pub(crate) fn validate_init_graph(
    registry: &SharedInitRegistry,
    graph: &InitDependencyGraph,
) -> Result<(), InitGraphError> {
    topological_order_indices(registry, graph).map(|_| ())
}

/// Topologically sort all registered init entrypoints.
///
/// Registered init functions that are not mentioned in `graph` are treated as
/// independent nodes and returned in registration order relative to other
/// ready-to-run nodes.
pub(crate) fn topological_sort_inits(
    registry: &SharedInitRegistry,
    graph: &InitDependencyGraph,
) -> Result<Vec<SharedInitEntry>, InitGraphError> {
    topological_order_indices(registry, graph).map(|order| {
        order
            .into_iter()
            .map(|idx| registry.entries[idx])
            .collect::<Vec<_>>()
    })
}

fn topological_order_indices(
    registry: &SharedInitRegistry,
    graph: &InitDependencyGraph,
) -> Result<Vec<usize>, InitGraphError> {
    let unknown = graph
        .referenced_names()
        .into_iter()
        .filter(|name| registry.get_init(name).is_none())
        .map(str::to_string)
        .collect::<Vec<_>>();
    if !unknown.is_empty() {
        return Err(InitGraphError::UnknownInits(unknown));
    }

    let mut in_degree = vec![0_usize; registry.len()];
    let mut outgoing = vec![Vec::<usize>::new(); registry.len()];

    for (name, deps) in &graph.dependencies {
        let name_idx = registry
            .index_of(name)
            .expect("graph validation should reject unknown init nodes");
        for dep in deps {
            let dep_idx = registry
                .index_of(dep)
                .expect("graph validation should reject unknown dependency nodes");
            outgoing[dep_idx].push(name_idx);
            in_degree[name_idx] += 1;
        }
    }

    let mut ready = BinaryHeap::new();
    for (idx, &degree) in in_degree.iter().enumerate() {
        if degree == 0 {
            ready.push(Reverse(idx));
        }
    }

    let mut order = Vec::with_capacity(registry.len());
    while let Some(Reverse(idx)) = ready.pop() {
        order.push(idx);
        for &next in &outgoing[idx] {
            in_degree[next] -= 1;
            if in_degree[next] == 0 {
                ready.push(Reverse(next));
            }
        }
    }

    if order.len() == registry.len() {
        return Ok(order);
    }

    let cycle = in_degree
        .iter()
        .enumerate()
        .filter(|(_, degree)| **degree > 0)
        .map(|(idx, _)| registry.entries[idx].name.to_string())
        .collect::<Vec<_>>();
    Err(InitGraphError::Cycle(cycle))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::Name;

    #[test]
    fn test_register_and_lookup_shared_inits() {
        let mut registry = SharedInitRegistry::new();
        assert!(register_init(
            &mut registry,
            "init_eq",
            Environment::init_eq
        ));
        assert!(register_init(
            &mut registry,
            "init_true_false",
            Environment::init_true_false
        ));
        assert!(!register_init(
            &mut registry,
            "init_eq",
            Environment::init_true_false
        ));

        let eq = get_init(&registry, "init_eq").expect("init_eq should be present");
        assert_eq!(eq.name, "init_eq");
        assert!(get_init(&registry, "init_missing").is_none());
        assert_eq!(registry.len(), 2);
        assert!(!registry.is_empty());
    }

    #[test]
    fn test_topological_sort_preserves_registration_order_for_independent_inits() {
        let mut registry = SharedInitRegistry::new();
        register_init(
            &mut registry,
            "init_true_false",
            Environment::init_true_false,
        );
        register_init(&mut registry, "init_eq", Environment::init_eq);
        register_init(&mut registry, "init_iff", Environment::init_iff);

        let order = topological_sort_inits(&registry, &InitDependencyGraph::new())
            .expect("independent shared init functions should sort");
        let names = order.iter().map(|entry| entry.name).collect::<Vec<_>>();
        assert_eq!(names, vec!["init_true_false", "init_eq", "init_iff"]);
    }

    #[test]
    fn test_topological_sort_respects_dependencies_and_executes() {
        let mut registry = SharedInitRegistry::new();
        register_init(&mut registry, "init_and", Environment::init_and);
        register_init(
            &mut registry,
            "init_true_false",
            Environment::init_true_false,
        );
        register_init(&mut registry, "init_eq", Environment::init_eq);

        let mut graph = InitDependencyGraph::new();
        graph.add_dependency("init_and", "init_true_false");
        graph.add_dependency("init_true_false", "init_eq");

        let order =
            topological_sort_inits(&registry, &graph).expect("shared init graph should sort");
        let names = order.iter().map(|entry| entry.name).collect::<Vec<_>>();
        assert_eq!(names, vec!["init_eq", "init_true_false", "init_and"]);

        let mut env = Environment::new();
        for entry in order {
            (entry.init_fn)(&mut env).expect("sorted init should execute successfully");
        }

        assert!(env.get_const(&Name::from_string("Eq")).is_some());
        assert!(env.get_const(&Name::from_string("True")).is_some());
        assert!(env.get_const(&Name::from_string("And")).is_some());
    }

    #[test]
    fn test_validate_init_graph_reports_cycles() {
        let mut registry = SharedInitRegistry::new();
        register_init(&mut registry, "init_a", Environment::init_eq);
        register_init(&mut registry, "init_b", Environment::init_true_false);

        let mut graph = InitDependencyGraph::new();
        graph.add_dependency("init_a", "init_b");
        graph.add_dependency("init_b", "init_a");

        let err =
            validate_init_graph(&registry, &graph).expect_err("mutual dependency should cycle");
        assert_eq!(
            err,
            InitGraphError::Cycle(vec!["init_a".to_string(), "init_b".to_string()])
        );
    }

    #[test]
    fn test_topological_sort_rejects_unknown_inits() {
        let mut registry = SharedInitRegistry::new();
        register_init(&mut registry, "init_eq", Environment::init_eq);

        let mut graph = InitDependencyGraph::new();
        graph.add_dependency("init_eq", "init_missing");

        let err = topological_sort_inits(&registry, &graph)
            .expect_err("unknown dependency should fail validation");
        assert_eq!(
            err,
            InitGraphError::UnknownInits(vec!["init_missing".to_string()])
        );
    }
}
