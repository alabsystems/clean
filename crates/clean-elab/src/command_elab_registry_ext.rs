// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended command elaboration registry: override tracking, usage statistics,
//! dependency analysis, namespace filtering, batch registration, snapshot/diff,
//! and validation.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

use crate::command_elab_registry::{CommandElabEntry, CommandElabRegistry};

/// Errors from extended registry operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum RegistryExtError {
    #[error("duplicate registration for command '{name}'")]
    DuplicateRegistration { name: String },
    #[error("command '{command}' depends on '{dependency}' which is not registered")]
    MissingDependency { command: String, dependency: String },
    #[error("circular dependency detected involving: {cycle}")]
    CircularDependency { cycle: String },
    #[error("batch conflict: command '{name}' already exists with priority {existing_priority}")]
    BatchConflict {
        name: String,
        existing_priority: u32,
    },
}

/// Record of a command override: what was replaced and by what.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OverrideRecord {
    pub(crate) command_name: String,
    pub(crate) original_priority: u32,
    pub(crate) replacement_priority: u32,
}

/// Tracks which commands have been overridden (multiple handlers where a
/// higher-priority handler shadows a lower one).
#[derive(Debug, Clone, Default)]
pub(crate) struct OverrideTracker {
    records: Vec<OverrideRecord>,
}

impl OverrideTracker {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(
        &mut self,
        command_name: &str,
        original_priority: u32,
        replacement_priority: u32,
    ) {
        self.records.push(OverrideRecord {
            command_name: command_name.to_owned(),
            original_priority,
            replacement_priority,
        });
    }

    #[must_use]
    pub(crate) fn records(&self) -> &[OverrideRecord] {
        &self.records
    }

    #[must_use]
    pub(crate) fn is_overridden(&self, command_name: &str) -> bool {
        self.records.iter().any(|r| r.command_name == command_name)
    }

    #[must_use]
    pub(crate) fn overridden_count(&self) -> usize {
        let names: HashSet<&str> = self
            .records
            .iter()
            .map(|r| r.command_name.as_str())
            .collect();
        names.len()
    }
}

/// Detect overrides in a registry by finding commands with 2+ handlers.
#[must_use]
pub(crate) fn detect_overrides(registry: &CommandElabRegistry) -> OverrideTracker {
    let mut tracker = OverrideTracker::new();
    for kind in registry.kinds() {
        if let Some(handlers) = registry.get_handlers(kind) {
            if handlers.len() >= 2 {
                let replacement = handlers[0].priority;
                for h in &handlers[1..] {
                    tracker.record(kind, h.priority, replacement);
                }
            }
        }
    }
    tracker
}

/// Per-command usage statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct CommandUsageStats {
    pub(crate) invocations: u64,
    pub(crate) successes: u64,
    pub(crate) failures: u64,
    pub(crate) total_duration: Duration,
}

impl CommandUsageStats {
    /// Average duration per invocation, or `None` if no invocations.
    #[must_use]
    pub(crate) fn avg_duration(&self) -> Option<Duration> {
        if self.invocations == 0 {
            return None;
        }
        Some(self.total_duration / self.invocations as u32)
    }

    /// Failure rate as a fraction in [0.0, 1.0], or `None` if no invocations.
    #[must_use]
    pub(crate) fn failure_rate(&self) -> Option<f64> {
        if self.invocations == 0 {
            return None;
        }
        Some(self.failures as f64 / self.invocations as f64)
    }
}

/// Collector for per-command usage statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct UsageCollector {
    stats: HashMap<String, CommandUsageStats>,
}

impl UsageCollector {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record_invocation(
        &mut self,
        command_name: &str,
        success: bool,
        duration: Duration,
    ) {
        let entry = self.stats.entry(command_name.to_owned()).or_default();
        entry.invocations += 1;
        if success {
            entry.successes += 1;
        } else {
            entry.failures += 1;
        }
        entry.total_duration += duration;
    }

    #[must_use]
    pub(crate) fn get(&self, command_name: &str) -> Option<&CommandUsageStats> {
        self.stats.get(command_name)
    }

    pub(crate) fn commands(&self) -> impl Iterator<Item = &str> {
        self.stats.keys().map(|s| s.as_str())
    }

    #[must_use]
    pub(crate) fn total_invocations(&self) -> u64 {
        self.stats.values().map(|s| s.invocations).sum()
    }

    #[must_use]
    pub(crate) fn active_command_count(&self) -> usize {
        self.stats.len()
    }

    pub(crate) fn reset(&mut self) {
        self.stats.clear();
    }
}

/// Declared dependency: command A requires command B to be registered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommandDependency {
    pub(crate) command: String,
    pub(crate) depends_on: String,
}

/// Validate that all declared dependencies are satisfied by the registry.
pub(crate) fn validate_dependencies(
    registry: &CommandElabRegistry,
    deps: &[CommandDependency],
) -> Result<(), RegistryExtError> {
    for dep in deps {
        if !registry.is_registered(&dep.depends_on) {
            return Err(RegistryExtError::MissingDependency {
                command: dep.command.clone(),
                dependency: dep.depends_on.clone(),
            });
        }
    }
    Ok(())
}

/// Detect circular dependencies via DFS. Returns `Ok(())` if acyclic.
pub(crate) fn detect_circular_dependencies(
    deps: &[CommandDependency],
) -> Result<(), RegistryExtError> {
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for dep in deps {
        adj.entry(dep.command.as_str())
            .or_default()
            .push(dep.depends_on.as_str());
    }

    let mut visited: HashSet<&str> = HashSet::new();
    let mut in_stack: HashSet<&str> = HashSet::new();

    fn dfs<'a>(
        node: &'a str,
        adj: &HashMap<&'a str, Vec<&'a str>>,
        visited: &mut HashSet<&'a str>,
        in_stack: &mut HashSet<&'a str>,
    ) -> Result<(), String> {
        if in_stack.contains(node) {
            return Err(node.to_owned());
        }
        if visited.contains(node) {
            return Ok(());
        }
        visited.insert(node);
        in_stack.insert(node);
        if let Some(neighbors) = adj.get(node) {
            for &neighbor in neighbors {
                dfs(neighbor, adj, visited, in_stack)?;
            }
        }
        in_stack.remove(node);
        Ok(())
    }

    for node in adj.keys() {
        dfs(node, &adj, &mut visited, &mut in_stack)
            .map_err(|cycle| RegistryExtError::CircularDependency { cycle })?;
    }
    Ok(())
}

/// Filter registry command names by a namespace prefix. Returns sorted results.
#[must_use]
pub(crate) fn filter_by_namespace(registry: &CommandElabRegistry, prefix: &str) -> Vec<String> {
    let mut result: Vec<String> = registry
        .kinds()
        .filter(|k| k.starts_with(prefix))
        .map(|k| k.to_owned())
        .collect();
    result.sort();
    result
}

/// Filter registry command names by a simple wildcard pattern.
///
/// Supports `*` at end (`"foo*"`), beginning (`"*bar"`), or alone (`"*"`).
/// No `*` means exact match.
#[must_use]
pub(crate) fn filter_by_wildcard(registry: &CommandElabRegistry, pattern: &str) -> Vec<String> {
    let mut result: Vec<String> = if pattern == "*" {
        registry.kinds().map(|k| k.to_owned()).collect()
    } else if let Some(prefix) = pattern.strip_suffix('*') {
        registry
            .kinds()
            .filter(|k| k.starts_with(prefix))
            .map(|k| k.to_owned())
            .collect()
    } else if let Some(suffix) = pattern.strip_prefix('*') {
        registry
            .kinds()
            .filter(|k| k.ends_with(suffix))
            .map(|k| k.to_owned())
            .collect()
    } else {
        registry
            .kinds()
            .filter(|k| *k == pattern)
            .map(|k| k.to_owned())
            .collect()
    };
    result.sort();
    result
}

/// Specification for a command to be registered in a batch.
#[derive(Clone)]
pub(crate) struct BatchEntry {
    pub(crate) name: String,
    pub(crate) handler: Arc<crate::command_elab_registry::CommandElabFn>,
    pub(crate) priority: u32,
}

impl std::fmt::Debug for BatchEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BatchEntry")
            .field("name", &self.name)
            .field("priority", &self.priority)
            .field("handler", &"<fn>")
            .finish()
    }
}

/// Mode for batch conflict resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BatchConflictMode {
    /// Reject the entire batch if any command already exists.
    Reject,
    /// Skip entries that already exist.
    Skip,
    /// Allow adding additional handlers (same as normal register).
    Allow,
}

/// Register multiple commands with conflict detection.
///
/// In `Reject` mode, none are registered if any conflict exists. In `Skip`
/// mode, conflicting entries are silently skipped. In `Allow` mode, all
/// entries are registered normally. Also checks for intra-batch duplicates.
pub(crate) fn batch_register(
    registry: &mut CommandElabRegistry,
    entries: &[BatchEntry],
    mode: BatchConflictMode,
) -> Result<usize, RegistryExtError> {
    let mut seen: HashSet<&str> = HashSet::new();
    for entry in entries {
        if !seen.insert(entry.name.as_str()) {
            return Err(RegistryExtError::DuplicateRegistration {
                name: entry.name.clone(),
            });
        }
    }
    if mode == BatchConflictMode::Reject {
        for entry in entries {
            if let Some(handlers) = registry.get_handlers(&entry.name) {
                if !handlers.is_empty() {
                    return Err(RegistryExtError::BatchConflict {
                        name: entry.name.clone(),
                        existing_priority: handlers[0].priority,
                    });
                }
            }
        }
    }
    let mut registered = 0;
    for entry in entries {
        if mode == BatchConflictMode::Skip && registry.is_registered(&entry.name) {
            continue;
        }
        registry.register(
            &entry.name,
            CommandElabEntry {
                command_name: entry.name.clone(),
                handler: Arc::clone(&entry.handler),
                priority: entry.priority,
            },
        );
        registered += 1;
    }
    Ok(registered)
}

/// A snapshot of registry state: command names with handler counts and top priorities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistrySnapshot {
    pub(crate) entries: BTreeMap<String, (usize, u32)>,
}

/// Take a snapshot of the current registry state.
#[must_use]
pub(crate) fn snapshot(registry: &CommandElabRegistry) -> RegistrySnapshot {
    let mut entries = BTreeMap::new();
    for kind in registry.kinds() {
        if let Some(handlers) = registry.get_handlers(kind) {
            if !handlers.is_empty() {
                entries.insert(kind.to_owned(), (handlers.len(), handlers[0].priority));
            }
        }
    }
    RegistrySnapshot { entries }
}

/// Diff between two registry snapshots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistryDiff {
    pub(crate) added: BTreeSet<String>,
    pub(crate) removed: BTreeSet<String>,
    pub(crate) changed: BTreeSet<String>,
}

impl RegistryDiff {
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.changed.is_empty()
    }

    #[must_use]
    pub(crate) fn total_changes(&self) -> usize {
        self.added.len() + self.removed.len() + self.changed.len()
    }
}

/// Compute the diff between two snapshots.
#[must_use]
pub(crate) fn diff_snapshots(before: &RegistrySnapshot, after: &RegistrySnapshot) -> RegistryDiff {
    let mut added = BTreeSet::new();
    let mut removed = BTreeSet::new();
    let mut changed = BTreeSet::new();
    for (name, val) in &after.entries {
        match before.entries.get(name) {
            None => {
                added.insert(name.clone());
            }
            Some(old_val) if old_val != val => {
                changed.insert(name.clone());
            }
            _ => {}
        }
    }
    for name in before.entries.keys() {
        if !after.entries.contains_key(name) {
            removed.insert(name.clone());
        }
    }
    RegistryDiff {
        added,
        removed,
        changed,
    }
}

/// Check for duplicate names. Returns the first duplicate found, or `Ok(())`.
pub(crate) fn check_duplicates(names: &[&str]) -> Result<(), RegistryExtError> {
    let mut seen = HashSet::new();
    for name in names {
        if !seen.insert(*name) {
            return Err(RegistryExtError::DuplicateRegistration {
                name: (*name).to_owned(),
            });
        }
    }
    Ok(())
}

/// Validate a registry: check declared dependencies are satisfied and acyclic.
pub(crate) fn validate_registry(
    registry: &CommandElabRegistry,
    deps: &[CommandDependency],
) -> Vec<RegistryExtError> {
    let mut errors = Vec::new();
    for dep in deps {
        if !registry.is_registered(&dep.depends_on) {
            errors.push(RegistryExtError::MissingDependency {
                command: dep.command.clone(),
                dependency: dep.depends_on.clone(),
            });
        }
    }
    if let Err(e) = detect_circular_dependencies(deps) {
        errors.push(e);
    }
    errors
}
