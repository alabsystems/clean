// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! Extended diamond resolution: path enumeration, coherence checking, resolution
//! strategies, statistics, visualization, cycle detection, and caching.
//!
//! Builds on [`super::diamond_resolution::DiamondDetector`] to provide richer
//! analysis and multiple resolution strategies for typeclass diamond inheritance.

use crate::diamond_resolution::{Diamond, DiamondDetector, DiamondError, InstanceEntry};
use clean_kernel::expr::Expr;
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

/// Errors specific to extended diamond resolution operations.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub(crate) enum DiamondExtError {
    #[error("cycle detected in instance graph involving classes: {}", classes.join(", "))]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    CycleDetected { classes: Vec<String> },
    #[error("no resolution strategy applicable for diamond at `{class}`")]
    NoApplicableStrategy { class: String },
    #[error("cache invalidated: instance database changed since last resolution")]
    CacheInvalidated,
    #[error(transparent)]
    Base(#[from] DiamondError),
}

/// Strategy for resolving ambiguous diamond paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ResolutionStrategy {
    /// Prefer the shortest path through the diamond.
    PreferShortest,
    /// Prefer paths containing explicitly registered instances.
    PreferExplicit,
    /// Prefer paths through locally-scoped (most recently registered) instances.
    PreferLocal,
}

/// Aggregate statistics about diamonds in a class hierarchy.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct DiamondStats {
    pub(crate) diamond_count: usize,
    pub(crate) max_depth: usize,
    pub(crate) max_branching_factor: usize,
    /// Distribution of branching factors: branching_factor -> count.
    pub(crate) branching_distribution: HashMap<usize, usize>,
    /// Total number of distinct paths across all diamonds.
    pub(crate) total_paths: usize,
}

/// Result of resolving a diamond via a specific strategy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedDiamond {
    pub(crate) class_name: String,
    pub(crate) chosen_path_index: usize,
    pub(crate) strategy_used: ResolutionStrategy,
    pub(crate) instance_expr: Expr,
}

/// Cache for resolved diamonds, invalidated when the instance database changes.
#[derive(Debug, Default)]
pub(crate) struct ResolutionCache {
    entries: HashMap<(String, String), ResolvedDiamond>,
    instance_fingerprint: u64,
}

impl ResolutionCache {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn get(
        &self,
        target: &str,
        ancestor: &str,
        current_fingerprint: u64,
    ) -> Result<Option<&ResolvedDiamond>, DiamondExtError> {
        if self.instance_fingerprint != current_fingerprint && !self.entries.is_empty() {
            return Err(DiamondExtError::CacheInvalidated);
        }
        Ok(self.entries.get(&(target.to_owned(), ancestor.to_owned())))
    }

    pub(crate) fn insert(
        &mut self,
        target: &str,
        ancestor: &str,
        resolved: ResolvedDiamond,
        fingerprint: u64,
    ) {
        self.instance_fingerprint = fingerprint;
        self.entries
            .insert((target.to_owned(), ancestor.to_owned()), resolved);
    }

    pub(crate) fn invalidate(&mut self) {
        self.entries.clear();
        self.instance_fingerprint = 0;
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Extended diamond resolver wrapping [`DiamondDetector`] with strategy-based
/// resolution, cycle detection, statistics, DOT visualization, and caching.
#[derive(Debug)]
pub(crate) struct DiamondResolverExt {
    pub(crate) detector: DiamondDetector,
    pub(crate) cache: ResolutionCache,
    instance_version: u64,
    explicit_instances: HashMap<String, HashSet<String>>,
}

impl DiamondResolverExt {
    pub(crate) fn new() -> Self {
        Self {
            detector: DiamondDetector::new(),
            cache: ResolutionCache::new(),
            instance_version: 0,
            explicit_instances: HashMap::new(),
        }
    }

    pub(crate) fn from_detector(detector: DiamondDetector) -> Self {
        Self {
            detector,
            cache: ResolutionCache::new(),
            instance_version: 0,
            explicit_instances: HashMap::new(),
        }
    }

    pub(crate) fn register_superclass(&mut self, class: &str, superclass: &str) {
        self.detector.register_superclass(class, superclass);
        self.cache.invalidate();
    }

    pub(crate) fn register_instance(&mut self, entry: InstanceEntry) {
        self.detector.register_instance(entry);
        self.instance_version += 1;
        self.cache.invalidate();
    }

    /// Register an instance and mark it as explicit (user-provided, not synthesized).
    pub(crate) fn register_explicit_instance(&mut self, entry: InstanceEntry) {
        let class = entry.class.clone();
        let name = entry.name.clone();
        self.register_instance(entry);
        self.explicit_instances
            .entry(class)
            .or_default()
            .insert(name);
    }

    pub(crate) fn instance_fingerprint(&self) -> u64 {
        self.instance_version
    }

    /// Enumerate all paths from `target` to `ancestor`, sorted shortest first.
    pub(crate) fn enumerate_paths(&self, target: &str, ancestor: &str) -> Vec<Vec<String>> {
        self.detector.find_all_paths(target, ancestor)
    }

    /// Count the number of distinct paths from `target` to `ancestor`.
    pub(crate) fn path_count(&self, target: &str, ancestor: &str) -> usize {
        self.detector.find_all_paths(target, ancestor).len()
    }

    /// Check coherence of all diamonds reachable from `target_class`.
    pub(crate) fn check_all_coherence(&self, target_class: &str) -> Vec<DiamondError> {
        self.detector
            .detect_diamonds(target_class)
            .iter()
            .filter_map(|d| self.detector.check_diamond_coherence(d).err())
            .collect()
    }

    /// Check coherence for a specific ancestor reached from `target_class`.
    pub(crate) fn check_coherence_for(
        &self,
        target_class: &str,
        ancestor: &str,
    ) -> Result<(), DiamondExtError> {
        let diamonds = self.detector.detect_diamonds(target_class);
        let diamond = diamonds
            .iter()
            .find(|d| d.class_name == ancestor)
            .ok_or_else(|| DiamondError::NoPaths {
                from: target_class.to_owned(),
                to: ancestor.to_owned(),
            })?;
        self.detector.check_diamond_coherence(diamond)?;
        Ok(())
    }

    /// Resolve a diamond using the given strategy.
    pub(crate) fn resolve_with_strategy(
        &mut self,
        target_class: &str,
        strategy: ResolutionStrategy,
    ) -> Result<Vec<ResolvedDiamond>, DiamondExtError> {
        let diamonds = self.detector.detect_diamonds(target_class);
        let mut results = Vec::new();
        for diamond in &diamonds {
            if diamond.instance_paths.is_empty() {
                continue;
            }
            results.push(self.apply_strategy(diamond, target_class, strategy)?);
        }
        Ok(results)
    }

    fn apply_strategy(
        &mut self,
        diamond: &Diamond,
        target_class: &str,
        strategy: ResolutionStrategy,
    ) -> Result<ResolvedDiamond, DiamondExtError> {
        let chosen_index = match strategy {
            ResolutionStrategy::PreferShortest => self.pick_shortest(diamond),
            ResolutionStrategy::PreferExplicit => self.pick_explicit(diamond),
            ResolutionStrategy::PreferLocal => self.pick_local(diamond),
        }
        .ok_or_else(|| DiamondExtError::NoApplicableStrategy {
            class: diamond.class_name.clone(),
        })?;
        let path = &diamond.instance_paths[chosen_index];
        let resolved = ResolvedDiamond {
            class_name: diamond.class_name.clone(),
            chosen_path_index: chosen_index,
            strategy_used: strategy,
            instance_expr: path.instance_expr.clone(),
        };
        self.cache.insert(
            target_class,
            &diamond.class_name,
            resolved.clone(),
            self.instance_version,
        );
        Ok(resolved)
    }

    fn pick_shortest(&self, diamond: &Diamond) -> Option<usize> {
        diamond
            .instance_paths
            .iter()
            .enumerate()
            .min_by_key(|(_, p)| p.through.len())
            .map(|(i, _)| i)
    }

    fn pick_explicit(&self, diamond: &Diamond) -> Option<usize> {
        let explicit_set = self.explicit_instances.get(&diamond.class_name);
        if let Some(instances) = self.detector.known_instances.get(&diamond.class_name) {
            for (i, _) in diamond.instance_paths.iter().enumerate() {
                let name = &instances[i % instances.len()].name;
                if explicit_set.map(|s| s.contains(name)).unwrap_or(false) {
                    return Some(i);
                }
            }
        }
        if diamond.instance_paths.is_empty() {
            None
        } else {
            Some(0)
        }
    }

    fn pick_local(&self, diamond: &Diamond) -> Option<usize> {
        if diamond.instance_paths.is_empty() {
            return None;
        }
        let instances = self.detector.known_instances.get(&diamond.class_name)?;
        if instances.is_empty() {
            return None;
        }
        Some(diamond.instance_paths.len() - 1)
    }

    /// Detect cycles in the class hierarchy using iterative DFS coloring.
    pub(crate) fn detect_cycles(&self) -> Vec<Vec<String>> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Color {
            White,
            Gray,
            Black,
        }

        let all: Vec<String> = self.detector.class_hierarchy.keys().cloned().collect();
        let mut color: HashMap<String, Color> =
            all.iter().map(|c| (c.clone(), Color::White)).collect();
        let mut cycles = Vec::new();

        for start in &all {
            if color[start] != Color::White {
                continue;
            }
            let mut stack = vec![(start.clone(), vec![start.clone()])];
            while let Some((node, path)) = stack.pop() {
                match color.get(&node).copied().unwrap_or(Color::White) {
                    Color::Black => continue,
                    Color::Gray => {
                        if let Some(pos) = path.iter().position(|n| n == &node) {
                            let cycle: Vec<String> = path[pos..].to_vec();
                            let is_self_loop = cycle.len() == 1
                                && self
                                    .detector
                                    .superclasses(&cycle[0])
                                    .contains(&cycle[0].as_str());
                            if cycle.len() > 1 || is_self_loop {
                                cycles.push(cycle);
                            }
                        }
                        continue;
                    }
                    Color::White => {}
                }
                color.insert(node.clone(), Color::Gray);
                let scs = self.detector.superclasses(&node);
                if scs.is_empty() {
                    color.insert(node.clone(), Color::Black);
                } else {
                    for sc in scs.iter().rev() {
                        let mut p = path.clone();
                        p.push(sc.to_string());
                        stack.push((sc.to_string(), p));
                    }
                }
            }
            for c in color.values_mut() {
                if *c == Color::Gray {
                    *c = Color::Black;
                }
            }
        }
        cycles
    }

    /// Returns true if the class hierarchy contains any cycles.
    pub(crate) fn has_cycles(&self) -> bool {
        !self.detect_cycles().is_empty()
    }

    /// Collect diamond statistics for the hierarchy rooted at `target_class`.
    pub(crate) fn compute_stats(&self, target_class: &str) -> DiamondStats {
        let diamonds = self.detector.detect_diamonds(target_class);
        let mut stats = DiamondStats {
            diamond_count: diamonds.len(),
            ..Default::default()
        };
        for diamond in &diamonds {
            stats.total_paths += diamond.instance_paths.len();
            let branching = self.path_count(target_class, &diamond.class_name);
            *stats.branching_distribution.entry(branching).or_insert(0) += 1;
            if branching > stats.max_branching_factor {
                stats.max_branching_factor = branching;
            }
            for path in &diamond.instance_paths {
                if path.through.len() > stats.max_depth {
                    stats.max_depth = path.through.len();
                }
            }
        }
        stats
    }

    /// Generate a DOT-format graph of the class hierarchy.
    pub(crate) fn to_dot(&self) -> String {
        let mut dot = String::from("digraph diamond_hierarchy {\n  rankdir=BT;\n");
        let mut diamond_classes: HashSet<String> = HashSet::new();
        for class in self.detector.class_hierarchy.keys() {
            for d in self.detector.detect_diamonds(class) {
                diamond_classes.insert(d.class_name.clone());
            }
        }
        let mut all: Vec<&String> = self.detector.class_hierarchy.keys().collect();
        all.sort();
        for class in &all {
            let style = if diamond_classes.contains(class.as_str()) {
                " [style=filled, fillcolor=lightyellow]"
            } else {
                ""
            };
            dot.push_str(&format!("  \"{}\"{style};\n", class));
        }
        for (class, supers) in &self.detector.class_hierarchy {
            for sc in supers {
                dot.push_str(&format!("  \"{}\" -> \"{}\";\n", class, sc));
            }
        }
        dot.push_str("}\n");
        dot
    }

    /// Generate a DOT-format subgraph showing only diamond paths from
    /// `target` to `ancestor`.
    pub(crate) fn diamond_subgraph_dot(&self, target: &str, ancestor: &str) -> String {
        let paths = self.enumerate_paths(target, ancestor);
        let mut dot = String::from("digraph diamond_subgraph {\n  rankdir=BT;\n");
        let mut nodes: HashSet<String> = HashSet::new();
        let mut edges: HashSet<(String, String)> = HashSet::new();
        for path in &paths {
            for node in path {
                nodes.insert(node.clone());
            }
            for w in path.windows(2) {
                edges.insert((w[0].clone(), w[1].clone()));
            }
        }
        let mut sorted_nodes: Vec<&String> = nodes.iter().collect();
        sorted_nodes.sort();
        for node in &sorted_nodes {
            let style = if node.as_str() == target {
                " [style=filled, fillcolor=lightblue]"
            } else if node.as_str() == ancestor {
                " [style=filled, fillcolor=lightyellow]"
            } else {
                ""
            };
            dot.push_str(&format!("  \"{}\"{style};\n", node));
        }
        let mut sorted_edges: Vec<&(String, String)> = edges.iter().collect();
        sorted_edges.sort();
        for (from, to) in sorted_edges {
            dot.push_str(&format!("  \"{}\" -> \"{}\";\n", from, to));
        }
        dot.push_str("}\n");
        dot
    }

    /// Detect and resolve all diamonds from `target_class` using the given strategy.
    pub(crate) fn resolve_all(
        &mut self,
        target_class: &str,
        strategy: ResolutionStrategy,
    ) -> (Vec<ResolvedDiamond>, Vec<DiamondExtError>) {
        let diamonds = self.detector.detect_diamonds(target_class);
        let mut resolved = Vec::new();
        let mut errors = Vec::new();
        for diamond in &diamonds {
            if diamond.instance_paths.is_empty() {
                continue;
            }
            match self.apply_strategy(diamond, target_class, strategy) {
                Ok(r) => resolved.push(r),
                Err(e) => errors.push(e),
            }
        }
        (resolved, errors)
    }
}

impl fmt::Display for DiamondStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "diamonds={}, max_depth={}, max_branching={}, total_paths={}",
            self.diamond_count, self.max_depth, self.max_branching_factor, self.total_paths
        )
    }
}
