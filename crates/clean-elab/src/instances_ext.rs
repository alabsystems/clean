// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended instance management for type class resolution.
//!
//! Builds on [`super::instances::InstanceTable`] with diagnostics: priority
//! conflict analysis, instance chain detection, orphan flagging, statistics,
//! diamond detection, structured search logging, and batch operations.
//!
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`

use crate::instances::{extract_class_app, InstanceTable};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::{HashMap, HashSet, VecDeque};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum InstanceExtError {
    #[error("priority conflict for class `{class}`: {count} instances at priority {priority}")]
    PriorityConflict {
        class: String,
        priority: u32,
        count: usize,
    },
    #[error("orphan instance `{instance}` for class `{class}`")]
    OrphanInstance { instance: String, class: String },
    #[error("class `{0}` not found")]
    ClassNotFound(String),
    #[error("instance `{0}` not found")]
    InstanceNotFound(String),
    #[error("duplicate instance `{name}` for class `{class}`")]
    DuplicateInstance { name: String, class: String },
    #[error("diamond detected for type `{target}` via {path_count} paths")]
    DiamondDetected { target: String, path_count: usize },
}

// ---------------------------------------------------------------------------
// Priority conflict analysis
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PriorityConflict {
    pub(crate) class: Name,
    pub(crate) priority: u32,
    pub(crate) instances: Vec<Name>,
}

/// Find priority conflicts: multiple instances at the same priority for a class.
pub(crate) fn find_priority_conflicts(table: &InstanceTable) -> Vec<PriorityConflict> {
    let mut conflicts = Vec::new();
    for class in table.classes() {
        let mut by_priority: HashMap<u32, Vec<Name>> = HashMap::new();
        for inst in table.get_instances(&class.name) {
            by_priority
                .entry(inst.priority)
                .or_default()
                .push(inst.name.clone());
        }
        for (priority, names) in &by_priority {
            if names.len() > 1 {
                conflicts.push(PriorityConflict {
                    class: class.name.clone(),
                    priority: *priority,
                    instances: names.clone(),
                });
            }
        }
    }
    conflicts.sort_by(|a, b| a.class.cmp(&b.class).then(a.priority.cmp(&b.priority)));
    conflicts
}

// ---------------------------------------------------------------------------
// Instance chains
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstanceChain {
    pub(crate) chain: Vec<Name>,
    pub(crate) instance_names: Vec<Name>,
}

impl InstanceChain {
    pub(crate) fn depth(&self) -> usize {
        self.chain.len().saturating_sub(1)
    }
}

/// Build class dependency edges from instance type arguments.
fn build_class_edges(table: &InstanceTable) -> HashMap<Name, Vec<(Name, Name)>> {
    let mut edges: HashMap<Name, Vec<(Name, Name)>> = HashMap::new();
    for class in table.classes() {
        for inst in table.get_instances(&class.name) {
            if let Some((_, args)) = extract_class_app(&inst.type_) {
                for arg in &args {
                    if let Some((dep, _)) = extract_class_app(arg) {
                        if table.get_class(&dep).is_some() {
                            edges
                                .entry(class.name.clone())
                                .or_default()
                                .push((dep, inst.name.clone()));
                        }
                    }
                }
            }
        }
    }
    edges
}

/// Find transitive instance chains of length >= `min_depth`.
pub(crate) fn find_instance_chains(table: &InstanceTable, min_depth: usize) -> Vec<InstanceChain> {
    let edges = build_class_edges(table);
    let mut chains = Vec::new();
    for class in table.classes() {
        let mut queue: VecDeque<(Vec<Name>, Vec<Name>)> = VecDeque::new();
        queue.push_back((vec![class.name.clone()], Vec::new()));
        while let Some((path, inst_names)) = queue.pop_front() {
            let current = path.last().expect("invariant: path non-empty");
            if let Some(neighbors) = edges.get(current) {
                for (next_class, inst_name) in neighbors {
                    if path.contains(next_class) {
                        continue;
                    }
                    let mut np = path.clone();
                    np.push(next_class.clone());
                    let mut ni = inst_names.clone();
                    ni.push(inst_name.clone());
                    if np.len().saturating_sub(1) >= min_depth {
                        chains.push(InstanceChain {
                            chain: np.clone(),
                            instance_names: ni.clone(),
                        });
                    }
                    if np.len() < 8 {
                        queue.push_back((np, ni));
                    }
                }
            }
        }
    }
    chains
}

// ---------------------------------------------------------------------------
// Orphan detection
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OrphanInstance {
    pub(crate) instance_name: Name,
    pub(crate) class_name: Name,
}

/// Flag instances where neither the class nor any type argument is local.
pub(crate) fn find_orphan_instances(
    table: &InstanceTable,
    local_names: &HashSet<Name>,
) -> Vec<OrphanInstance> {
    let mut orphans = Vec::new();
    for class in table.classes() {
        if local_names.contains(&class.name) {
            continue;
        }
        for inst in table.get_instances(&class.name) {
            let has_local_arg = extract_class_app(&inst.type_)
                .map(|(_, args)| {
                    args.iter().any(|a| {
                        extract_class_app(a).is_some_and(|(n, _)| local_names.contains(&n))
                    })
                })
                .unwrap_or(false);
            if !has_local_arg {
                orphans.push(OrphanInstance {
                    instance_name: inst.name.clone(),
                    class_name: class.name.clone(),
                });
            }
        }
    }
    orphans
}

// ---------------------------------------------------------------------------
// Instance statistics
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ClassStats {
    pub(crate) class_name: Name,
    pub(crate) instance_count: usize,
    pub(crate) avg_priority: f64,
    pub(crate) min_priority: u32,
    pub(crate) max_priority: u32,
    pub(crate) has_out_params: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct InstanceStatistics {
    pub(crate) total_classes: usize,
    pub(crate) total_instances: usize,
    pub(crate) per_class: Vec<ClassStats>,
    pub(crate) depth_distribution: HashMap<usize, usize>,
}

pub(crate) fn collect_statistics(table: &InstanceTable) -> InstanceStatistics {
    let mut per_class = Vec::new();
    let mut depth_dist: HashMap<usize, usize> = HashMap::new();
    let mut total_instances = 0usize;
    for class in table.classes() {
        let insts = table.get_instances(&class.name);
        let count = insts.len();
        total_instances += count;
        *depth_dist.entry(count).or_insert(0) += 1;
        let (min_p, max_p, sum_p) = if insts.is_empty() {
            (0u32, 0u32, 0u64)
        } else {
            insts.iter().fold((u32::MAX, 0u32, 0u64), |(mn, mx, s), i| {
                (
                    mn.min(i.priority),
                    mx.max(i.priority),
                    s + u64::from(i.priority),
                )
            })
        };
        per_class.push(ClassStats {
            class_name: class.name.clone(),
            instance_count: count,
            avg_priority: if count > 0 {
                sum_p as f64 / count as f64
            } else {
                0.0
            },
            min_priority: if insts.is_empty() { 0 } else { min_p },
            max_priority: max_p,
            has_out_params: !class.out_params.is_empty(),
        });
    }
    per_class.sort_by(|a, b| a.class_name.cmp(&b.class_name));
    InstanceStatistics {
        total_classes: table.num_classes(),
        total_instances,
        per_class,
        depth_distribution: depth_dist,
    }
}

// ---------------------------------------------------------------------------
// Diamond detection
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstanceDiamond {
    pub(crate) target_class: Name,
    pub(crate) paths: Vec<Vec<Name>>,
}

/// Find diamonds: classes reachable via 2+ distinct dependency paths.
pub(crate) fn detect_diamonds(table: &InstanceTable) -> Vec<InstanceDiamond> {
    let edges = build_class_edges(table);
    let dep_map: HashMap<Name, Vec<Name>> = edges
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().map(|(cls, _)| cls).collect()))
        .collect();
    let mut diamonds = Vec::new();
    for class in table.classes() {
        let mut paths_to: HashMap<Name, Vec<Vec<Name>>> = HashMap::new();
        let mut queue: VecDeque<Vec<Name>> = VecDeque::new();
        queue.push_back(vec![class.name.clone()]);
        while let Some(path) = queue.pop_front() {
            let current = path.last().expect("invariant: path non-empty");
            if let Some(neighbors) = dep_map.get(current) {
                for next in neighbors {
                    if path.contains(next) {
                        continue;
                    }
                    let mut np = path.clone();
                    np.push(next.clone());
                    paths_to.entry(next.clone()).or_default().push(np.clone());
                    if np.len() < 8 {
                        queue.push_back(np);
                    }
                }
            }
        }
        for (target, paths) in &paths_to {
            if paths.len() > 1 {
                diamonds.push(InstanceDiamond {
                    target_class: target.clone(),
                    paths: paths.clone(),
                });
            }
        }
    }
    diamonds.sort_by(|a, b| a.target_class.cmp(&b.target_class));
    diamonds.dedup_by(|a, b| a.target_class == b.target_class);
    diamonds
}

// ---------------------------------------------------------------------------
// Search logging
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SearchEntry {
    pub(crate) class: Name,
    pub(crate) instance_tried: Name,
    pub(crate) outcome: SearchOutcome,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SearchOutcome {
    Success,
    Failure,
    Backtrack,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct SearchLog {
    entries: Vec<SearchEntry>,
}

impl SearchLog {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(&mut self, class: Name, instance_tried: Name, outcome: SearchOutcome) {
        self.entries.push(SearchEntry {
            class,
            instance_tried,
            outcome,
        });
    }

    pub(crate) fn entries(&self) -> &[SearchEntry] {
        &self.entries
    }

    fn count_outcome(&self, o: SearchOutcome) -> usize {
        self.entries.iter().filter(|e| e.outcome == o).count()
    }
    pub(crate) fn success_count(&self) -> usize {
        self.count_outcome(SearchOutcome::Success)
    }
    pub(crate) fn failure_count(&self) -> usize {
        self.count_outcome(SearchOutcome::Failure)
    }
    pub(crate) fn backtrack_count(&self) -> usize {
        self.count_outcome(SearchOutcome::Backtrack)
    }
    pub(crate) fn total(&self) -> usize {
        self.entries.len()
    }
    pub(crate) fn summary(&self) -> (usize, usize, usize) {
        (
            self.success_count(),
            self.failure_count(),
            self.backtrack_count(),
        )
    }
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

// ---------------------------------------------------------------------------
// Batch operations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct InstanceSpec {
    pub(crate) name: Name,
    pub(crate) class_name: Name,
    pub(crate) expr: Expr,
    pub(crate) type_: Expr,
    pub(crate) priority: u32,
}

#[derive(Debug, Clone)]
pub(crate) struct BatchResult {
    pub(crate) added: usize,
    pub(crate) conflicts: Vec<InstanceExtError>,
}

/// Add multiple instances, reporting duplicate-name conflicts without aborting.
pub(crate) fn batch_add(table: &mut InstanceTable, specs: &[InstanceSpec]) -> BatchResult {
    let mut added = 0usize;
    let mut conflicts = Vec::new();
    for spec in specs {
        if table
            .get_instances(&spec.class_name)
            .iter()
            .any(|i| i.name == spec.name)
        {
            conflicts.push(InstanceExtError::DuplicateInstance {
                name: format!("{:?}", spec.name),
                class: format!("{:?}", spec.class_name),
            });
            continue;
        }
        table.add_instance(
            spec.name.clone(),
            spec.class_name.clone(),
            spec.expr.clone(),
            spec.type_.clone(),
            spec.priority,
        );
        added += 1;
    }
    BatchResult { added, conflicts }
}

/// Count instances that *would* be removed by name.
///
/// `InstanceTable` does not expose a remove API, so this returns the match
/// count. Callers needing actual removal should rebuild the table.
pub(crate) fn batch_remove(table: &mut InstanceTable, names: &HashSet<Name>) -> usize {
    let class_names: Vec<Name> = table.classes().map(|c| c.name.clone()).collect();
    let mut removed = 0usize;
    for cn in &class_names {
        removed += table
            .get_instances(cn)
            .iter()
            .filter(|i| names.contains(&i.name))
            .count();
    }
    removed
}

/// Replace an instance: verify old exists, then add the new spec.
pub(crate) fn replace_instance(
    table: &mut InstanceTable,
    old_name: &Name,
    new_spec: &InstanceSpec,
) -> Result<(), InstanceExtError> {
    let found = table.classes().any(|c| {
        table
            .get_instances(&c.name)
            .iter()
            .any(|i| &i.name == old_name)
    });
    if !found {
        return Err(InstanceExtError::InstanceNotFound(format!("{old_name:?}")));
    }
    table.add_instance(
        new_spec.name.clone(),
        new_spec.class_name.clone(),
        new_spec.expr.clone(),
        new_spec.type_.clone(),
        new_spec.priority,
    );
    Ok(())
}
