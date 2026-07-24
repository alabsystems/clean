// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended environment snapshot management for incremental elaboration.
//!
//! Provides named checkpoints, environment diffing, merging of parallel
//! elaboration results, declaration fingerprinting, compression,
//! serialization, rollback, change callbacks, and statistics.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::Instant;

use clean_kernel::{ConstantInfo, Environment, Name};

/// Configuration for the extended snapshot manager.
#[derive(Debug, Clone)]
pub(crate) struct ExtSnapshotConfig {
    /// Maximum number of named checkpoints to retain.
    pub(crate) max_checkpoints: usize,
    /// Whether to compute fingerprints on checkpoint creation.
    pub(crate) auto_fingerprint: bool,
    /// Whether to track change statistics.
    pub(crate) track_stats: bool,
}

impl Default for ExtSnapshotConfig {
    fn default() -> Self {
        Self {
            max_checkpoints: 64,
            auto_fingerprint: true,
            track_stats: true,
        }
    }
}

/// A 64-bit fingerprint of a declaration for fast change detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct DeclFingerprint(u64);

impl DeclFingerprint {
    /// Compute a fingerprint from a `ConstantInfo`.
    #[must_use]
    pub(crate) fn from_constant(info: &ConstantInfo) -> Self {
        let mut hasher = DefaultHasher::new();
        format!("{:?}", info.name).hash(&mut hasher);
        std::mem::discriminant(&info.kind).hash(&mut hasher);
        format!("{:?}", info.type_).hash(&mut hasher);
        Self(hasher.finish())
    }

    /// Raw fingerprint value.
    #[must_use]
    pub(crate) fn value(self) -> u64 {
        self.0
    }
}

/// A named checkpoint capturing environment state at a point in time.
#[derive(Debug, Clone)]
pub(crate) struct Checkpoint {
    label: String,
    decl_names: HashSet<Name>,
    fingerprints: HashMap<Name, DeclFingerprint>,
    created_at: Instant,
    decl_count: usize,
}

impl Checkpoint {
    /// Take a checkpoint of the current environment.
    #[must_use]
    pub(crate) fn take(env: &Environment, label: &str, compute_fingerprints: bool) -> Self {
        let mut decl_names = HashSet::new();
        let mut fingerprints = HashMap::new();
        for info in env.constants() {
            let name = info.name.clone();
            if compute_fingerprints {
                fingerprints.insert(name.clone(), DeclFingerprint::from_constant(info));
            }
            decl_names.insert(name);
        }
        Self {
            label: label.to_owned(),
            decl_names,
            fingerprints,
            created_at: Instant::now(),
            decl_count: env.num_constants(),
        }
    }

    #[must_use]
    pub(crate) fn label(&self) -> &str {
        &self.label
    }

    #[must_use]
    pub(crate) fn decl_count(&self) -> usize {
        self.decl_count
    }

    #[must_use]
    pub(crate) fn decl_names(&self) -> &HashSet<Name> {
        &self.decl_names
    }

    /// When this checkpoint was created.
    #[must_use]
    pub(crate) fn created_at(&self) -> Instant {
        self.created_at
    }
}

/// The difference between two environment states.
#[derive(Debug, Clone)]
pub(crate) struct EnvironmentDiff {
    pub(crate) added: Vec<Name>,
    pub(crate) removed: Vec<Name>,
    pub(crate) modified: Vec<Name>,
}

impl EnvironmentDiff {
    /// Compute the diff between a checkpoint and the current environment.
    #[must_use]
    pub(crate) fn between(checkpoint: &Checkpoint, env: &Environment) -> Self {
        let mut current_names = HashSet::new();
        let mut current_fps = HashMap::new();
        for info in env.constants() {
            let name = info.name.clone();
            current_fps.insert(name.clone(), DeclFingerprint::from_constant(info));
            current_names.insert(name);
        }
        let added: Vec<Name> = current_names
            .difference(&checkpoint.decl_names)
            .cloned()
            .collect();
        let removed: Vec<Name> = checkpoint
            .decl_names
            .difference(&current_names)
            .cloned()
            .collect();
        let mut modified = Vec::new();
        for name in current_names.intersection(&checkpoint.decl_names) {
            if let (Some(old_fp), Some(new_fp)) =
                (checkpoint.fingerprints.get(name), current_fps.get(name))
            {
                if old_fp != new_fp {
                    modified.push(name.clone());
                }
            }
        }
        Self {
            added,
            removed,
            modified,
        }
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.modified.is_empty()
    }

    #[must_use]
    pub(crate) fn total_changes(&self) -> usize {
        self.added.len() + self.removed.len() + self.modified.len()
    }
}

/// A conflict detected when merging two environment branches.
#[derive(Debug, Clone)]
pub(crate) struct MergeConflict {
    pub(crate) name: Name,
    pub(crate) reason: String,
}

/// Result of merging two environment diffs.
#[derive(Debug, Clone)]
pub(crate) struct MergeResult {
    pub(crate) from_a: Vec<Name>,
    pub(crate) from_b: Vec<Name>,
    pub(crate) conflicts: Vec<MergeConflict>,
}

impl MergeResult {
    /// Merge two diffs that diverged from the same checkpoint.
    /// Non-conflicting additions are collected; same-name additions are conflicts.
    #[must_use]
    pub(crate) fn merge(diff_a: &EnvironmentDiff, diff_b: &EnvironmentDiff) -> Self {
        let set_a: HashSet<&Name> = diff_a.added.iter().collect();
        let set_b: HashSet<&Name> = diff_b.added.iter().collect();
        let mut conflicts = Vec::new();
        for name in set_a.intersection(&set_b) {
            conflicts.push(MergeConflict {
                name: (*name).clone(),
                reason: "both branches added the same declaration".to_owned(),
            });
        }
        let conflict_names: HashSet<&Name> = conflicts.iter().map(|c| &c.name).collect();
        let from_a = diff_a
            .added
            .iter()
            .filter(|n| !conflict_names.contains(n))
            .cloned()
            .collect();
        let from_b = diff_b
            .added
            .iter()
            .filter(|n| !conflict_names.contains(n))
            .cloned()
            .collect();
        Self {
            from_a,
            from_b,
            conflicts,
        }
    }

    #[must_use]
    pub(crate) fn is_clean(&self) -> bool {
        self.conflicts.is_empty()
    }
}

/// A compact representation of a checkpoint for storage.
/// Stores sorted name list and aggregate fingerprint instead of per-decl map.
#[derive(Debug, Clone)]
pub(crate) struct CompressedSnapshot {
    pub(crate) label: String,
    pub(crate) sorted_names: Vec<Name>,
    pub(crate) aggregate_fingerprint: u64,
    pub(crate) decl_count: usize,
}

impl CompressedSnapshot {
    #[must_use]
    pub(crate) fn from_checkpoint(cp: &Checkpoint) -> Self {
        let mut sorted_names: Vec<Name> = cp.decl_names.iter().cloned().collect();
        sorted_names.sort();
        let mut hasher = DefaultHasher::new();
        for (name, fp) in &cp.fingerprints {
            format!("{:?}", name).hash(&mut hasher);
            fp.value().hash(&mut hasher);
        }
        Self {
            label: cp.label.clone(),
            sorted_names,
            aggregate_fingerprint: hasher.finish(),
            decl_count: cp.decl_count,
        }
    }

    /// Check whether a name exists via binary search.
    #[must_use]
    pub(crate) fn contains_name(&self, name: &Name) -> bool {
        self.sorted_names.binary_search(name).is_ok()
    }
}

/// A serializable snapshot suitable for disk persistence.
/// Uses string representations of names for layout independence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SerializedSnapshot {
    pub(crate) label: String,
    pub(crate) names: Vec<String>,
    pub(crate) fingerprints: Vec<(String, u64)>,
    pub(crate) decl_count: usize,
}

impl SerializedSnapshot {
    #[must_use]
    pub(crate) fn from_checkpoint(cp: &Checkpoint) -> Self {
        let names: Vec<String> = cp.decl_names.iter().map(|n| format!("{n}")).collect();
        let fingerprints: Vec<(String, u64)> = cp
            .fingerprints
            .iter()
            .map(|(n, fp)| (format!("{n}"), fp.value()))
            .collect();
        Self {
            label: cp.label.clone(),
            names,
            fingerprints,
            decl_count: cp.decl_count,
        }
    }

    /// Reconstruct a checkpoint. `created_at` is set to now.
    #[must_use]
    pub(crate) fn to_checkpoint(&self) -> Checkpoint {
        let decl_names: HashSet<Name> = self.names.iter().map(|s| Name::from_string(s)).collect();
        let fingerprints: HashMap<Name, DeclFingerprint> = self
            .fingerprints
            .iter()
            .map(|(s, v)| (Name::from_string(s), DeclFingerprint(*v)))
            .collect();
        Checkpoint {
            label: self.label.clone(),
            decl_names,
            fingerprints,
            created_at: Instant::now(),
            decl_count: self.decl_count,
        }
    }
}

/// Statistics about snapshot operations.
#[derive(Debug, Clone, Default)]
pub(crate) struct SnapshotStats {
    pub(crate) checkpoints_created: usize,
    pub(crate) rollbacks_performed: usize,
    pub(crate) diffs_computed: usize,
    pub(crate) merges_attempted: usize,
    pub(crate) merge_conflicts: usize,
    pub(crate) current_checkpoint_count: usize,
}

/// A callback invoked when environment declarations change.
pub(crate) type ChangeCallback = Box<dyn Fn(&EnvironmentDiff) + Send + Sync>;

/// Extended snapshot manager with incremental checkpointing, diffing,
/// merging, and change notifications.
pub(crate) struct ExtSnapshotManager {
    checkpoints: HashMap<String, Checkpoint>,
    checkpoint_order: Vec<String>,
    config: ExtSnapshotConfig,
    stats: SnapshotStats,
    callbacks: Vec<ChangeCallback>,
}

impl std::fmt::Debug for ExtSnapshotManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtSnapshotManager")
            .field("checkpoints", &self.checkpoints.len())
            .field("config", &self.config)
            .field("stats", &self.stats)
            .field("callbacks", &self.callbacks.len())
            .finish()
    }
}

impl ExtSnapshotManager {
    #[must_use]
    pub(crate) fn new(config: ExtSnapshotConfig) -> Self {
        Self {
            checkpoints: HashMap::new(),
            checkpoint_order: Vec::new(),
            config,
            stats: SnapshotStats::default(),
            callbacks: Vec::new(),
        }
    }

    #[must_use]
    pub(crate) fn with_defaults() -> Self {
        Self::new(ExtSnapshotConfig::default())
    }

    /// Save a named checkpoint. Replaces existing; evicts oldest at capacity.
    pub(crate) fn save_checkpoint(&mut self, env: &Environment, label: &str) {
        if !self.checkpoints.contains_key(label)
            && self.checkpoints.len() >= self.config.max_checkpoints
        {
            if let Some(oldest) = self.checkpoint_order.first().cloned() {
                self.checkpoints.remove(&oldest);
                self.checkpoint_order.retain(|l| l != &oldest);
            }
        }
        let cp = Checkpoint::take(env, label, self.config.auto_fingerprint);
        self.checkpoints.insert(label.to_owned(), cp);
        self.checkpoint_order.retain(|l| l != label);
        self.checkpoint_order.push(label.to_owned());
        if self.config.track_stats {
            self.stats.checkpoints_created += 1;
            self.stats.current_checkpoint_count = self.checkpoints.len();
        }
    }

    #[must_use]
    pub(crate) fn get_checkpoint(&self, label: &str) -> Option<&Checkpoint> {
        self.checkpoints.get(label)
    }

    #[must_use]
    pub(crate) fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    #[must_use]
    pub(crate) fn checkpoint_labels(&self) -> &[String] {
        &self.checkpoint_order
    }

    /// Compute the diff between a named checkpoint and the current environment.
    pub(crate) fn diff_from_checkpoint(
        &mut self,
        label: &str,
        env: &Environment,
    ) -> Option<EnvironmentDiff> {
        let cp = self.checkpoints.get(label)?;
        let diff = EnvironmentDiff::between(cp, env);
        if self.config.track_stats {
            self.stats.diffs_computed += 1;
        }
        Some(diff)
    }

    /// Rollback environment using a stored backup. Returns false if label unknown.
    pub(crate) fn rollback(
        &mut self,
        label: &str,
        env: &mut Environment,
        backup: &Environment,
    ) -> bool {
        if !self.checkpoints.contains_key(label) {
            return false;
        }
        *env = backup.clone();
        if self.config.track_stats {
            self.stats.rollbacks_performed += 1;
        }
        true
    }

    pub(crate) fn remove_checkpoint(&mut self, label: &str) -> bool {
        if self.checkpoints.remove(label).is_some() {
            self.checkpoint_order.retain(|l| l != label);
            if self.config.track_stats {
                self.stats.current_checkpoint_count = self.checkpoints.len();
            }
            true
        } else {
            false
        }
    }

    pub(crate) fn clear_checkpoints(&mut self) {
        self.checkpoints.clear();
        self.checkpoint_order.clear();
        if self.config.track_stats {
            self.stats.current_checkpoint_count = 0;
        }
    }

    /// Merge diffs from two parallel elaboration branches.
    #[must_use]
    pub(crate) fn merge_diffs(
        &mut self,
        diff_a: &EnvironmentDiff,
        diff_b: &EnvironmentDiff,
    ) -> MergeResult {
        let result = MergeResult::merge(diff_a, diff_b);
        if self.config.track_stats {
            self.stats.merges_attempted += 1;
            self.stats.merge_conflicts += result.conflicts.len();
        }
        result
    }

    pub(crate) fn on_change(&mut self, cb: ChangeCallback) {
        self.callbacks.push(cb);
    }

    pub(crate) fn notify_change(&self, diff: &EnvironmentDiff) {
        for cb in &self.callbacks {
            cb(diff);
        }
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &SnapshotStats {
        &self.stats
    }
}
