// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment snapshotting and rollback for speculative elaboration.
//!
//! During elaboration the elaborator sometimes needs to try an approach
//! speculatively and, if it fails, roll back the environment to its
//! previous state.  This module provides [`EnvSnapshot`] for capturing
//! lightweight metadata about the environment at a point in time, and
//! [`EnvSnapshotManager`] for managing a LIFO stack of snapshots with
//! a configurable depth limit.
//!
//! The core speculative-execution primitive is
//! [`EnvSnapshotManager::speculative`], which clones the environment,
//! runs a closure, and either keeps the changes (on success) or restores
//! the clone (on failure).
//!
//! # Example
//!
//! ```text
//! let mut mgr = EnvSnapshotManager::new(8);
//! let snap = EnvSnapshot::take(&env);
//! mgr.push_snapshot(snap);
//!
//! let result = mgr.speculative(&mut env, |e| {
//!     // try something that might fail …
//!     Ok(42)
//! });
//! ```

use std::collections::HashSet;
use std::time::{Duration, Instant};

use crate::error::ElabError;
use clean_kernel::Environment;

// ---------------------------------------------------------------------------
// EnvSnapshot
// ---------------------------------------------------------------------------

/// A lightweight snapshot of environment state for rollback.
///
/// Captures counts and key-sets rather than a full clone so that callers can
/// inspect what the environment looked like at snapshot time without paying
/// for a deep copy.
#[derive(Debug, Clone)]
pub(crate) struct EnvSnapshot {
    /// Number of declarations (constants) at snapshot time.
    decl_count: usize,
    /// Number of registered simp lemmas.
    simp_lemma_count: usize,
    /// Number of registered type-class instances.
    instance_count: usize,
    /// Number of registered aesop rules (safe + unsafe + norm).
    aesop_rule_count: usize,
    /// Set of option keys that existed at snapshot time.
    option_keys: HashSet<String>,
    /// When the snapshot was taken.
    timestamp: Instant,
}

impl EnvSnapshot {
    /// Capture a snapshot of the current environment state.
    ///
    /// # REQUIRES
    /// - `env` is a valid `Environment`.
    ///
    /// # ENSURES
    /// - Returns an `EnvSnapshot` whose counts reflect the current env.
    #[must_use]
    pub(crate) fn take(env: &Environment) -> Self {
        let aesop_rule_count = env.get_aesop_safe_rules().len()
            + env.get_aesop_unsafe_rules().len()
            + env.get_aesop_norm_rules().len();

        // Collect option keys by iterating the options HashMap via get_option
        // Since Environment doesn't expose an iterator over all option keys,
        // we capture an empty set here. Callers who need full option tracking
        // should maintain their own key set.
        let option_keys = HashSet::new();

        Self {
            decl_count: env.num_constants(),
            simp_lemma_count: env.get_simp_lemmas().count(),
            instance_count: env.num_instances(),
            aesop_rule_count,
            option_keys,
            timestamp: Instant::now(),
        }
    }

    /// Capture a snapshot with an explicit set of known option keys.
    ///
    /// Use this variant when the caller maintains a set of option keys
    /// and wants to include them in the snapshot for later comparison.
    #[must_use]
    pub(crate) fn take_with_options(env: &Environment, option_keys: HashSet<String>) -> Self {
        let mut snap = Self::take(env);
        snap.option_keys = option_keys;
        snap
    }

    /// Number of declarations at snapshot time.
    #[must_use]
    pub(crate) fn decl_count(&self) -> usize {
        self.decl_count
    }

    /// Number of simp lemmas at snapshot time.
    #[must_use]
    pub(crate) fn simp_lemma_count(&self) -> usize {
        self.simp_lemma_count
    }

    /// Number of type-class instances at snapshot time.
    #[must_use]
    pub(crate) fn instance_count(&self) -> usize {
        self.instance_count
    }

    /// Number of aesop rules at snapshot time.
    #[must_use]
    pub(crate) fn aesop_rule_count(&self) -> usize {
        self.aesop_rule_count
    }

    /// The option keys that existed at snapshot time.
    #[must_use]
    pub(crate) fn option_keys(&self) -> &HashSet<String> {
        &self.option_keys
    }

    /// Time elapsed since this snapshot was taken.
    #[must_use]
    pub(crate) fn age(&self) -> Duration {
        self.timestamp.elapsed()
    }
}

// ---------------------------------------------------------------------------
// SpeculativeResult
// ---------------------------------------------------------------------------

/// Result of a speculative elaboration attempt.
#[derive(Debug)]
pub(crate) enum SpeculativeResult<T> {
    /// Elaboration succeeded; environment changes are kept.
    Success(T),
    /// Elaboration failed; environment was rolled back.
    Failure {
        /// The error from the failed elaboration.
        error: ElabError,
        /// The snapshot that was captured before speculation.
        snapshot: EnvSnapshot,
    },
    /// Partial success: the closure returned `Ok` but also produced warnings.
    Partial {
        /// The value produced by the closure.
        result: T,
        /// Warnings emitted during speculation.
        warnings: Vec<String>,
    },
}

// ---------------------------------------------------------------------------
// EnvSnapshotManager
// ---------------------------------------------------------------------------

/// Manager for a bounded LIFO stack of environment snapshots.
///
/// The manager enforces a maximum depth to prevent unbounded memory growth
/// when snapshots are pushed but never consumed.  When the limit is reached,
/// the oldest snapshot is silently discarded.
#[derive(Debug)]
pub(crate) struct EnvSnapshotManager {
    /// LIFO stack of snapshots.
    snapshots: Vec<EnvSnapshot>,
    /// Maximum number of snapshots to retain.
    max_snapshots: usize,
}

impl EnvSnapshotManager {
    /// Create a new snapshot manager.
    ///
    /// # Arguments
    /// * `max_snapshots` – upper bound on the number of retained snapshots.
    ///   A value of 0 is treated as 1 (at least one snapshot must be allowed).
    ///
    /// # ENSURES
    /// - `self.snapshot_count() == 0`
    /// - `self.max_snapshots >= 1`
    #[must_use]
    pub(crate) fn new(max_snapshots: usize) -> Self {
        Self {
            snapshots: Vec::new(),
            max_snapshots: max_snapshots.max(1),
        }
    }

    /// Push a snapshot onto the stack.
    ///
    /// If the stack is already at capacity, the oldest (bottom) snapshot is
    /// removed to make room.
    ///
    /// # ENSURES
    /// - `self.snapshot_count() <= self.max_snapshots`
    /// - The pushed snapshot is the most recent (`peek_snapshot` returns it).
    pub(crate) fn push_snapshot(&mut self, snapshot: EnvSnapshot) {
        if self.snapshots.len() >= self.max_snapshots {
            // Remove the oldest snapshot (index 0).
            self.snapshots.remove(0);
        }
        self.snapshots.push(snapshot);
    }

    /// Pop and return the most recent snapshot, or `None` if empty.
    ///
    /// # ENSURES
    /// - On `Some`, `self.snapshot_count()` decreases by 1.
    /// - On `None`, the manager was already empty.
    pub(crate) fn pop_snapshot(&mut self) -> Option<EnvSnapshot> {
        self.snapshots.pop()
    }

    /// Peek at the most recent snapshot without consuming it.
    #[must_use]
    pub(crate) fn peek_snapshot(&self) -> Option<&EnvSnapshot> {
        self.snapshots.last()
    }

    /// Number of snapshots currently retained.
    #[must_use]
    pub(crate) fn snapshot_count(&self) -> usize {
        self.snapshots.len()
    }

    /// Discard all snapshots.
    ///
    /// # ENSURES
    /// - `self.snapshot_count() == 0`
    pub(crate) fn clear(&mut self) {
        self.snapshots.clear();
    }

    /// Run a closure speculatively against the environment.
    ///
    /// 1. Takes a snapshot of `env`.
    /// 2. Clones `env` as a restore point.
    /// 3. Runs `f(env)`.
    /// 4. On `Ok(value)`, keeps the mutated `env` and returns
    ///    `SpeculativeResult::Success(value)`.
    /// 5. On `Err(e)`, restores `env` from the clone and returns
    ///    `SpeculativeResult::Failure { error, snapshot }`.
    ///
    /// The snapshot is pushed onto the manager stack only on failure so
    /// that callers can inspect what the environment looked like before
    /// the failed attempt.
    ///
    /// # REQUIRES
    /// - `env` is a valid mutable `Environment`.
    ///
    /// # ENSURES
    /// - On success, `env` contains all mutations made by `f`.
    /// - On failure, `env` is identical to its state before this call.
    pub(crate) fn speculative<F, T>(&mut self, env: &mut Environment, f: F) -> SpeculativeResult<T>
    where
        F: FnOnce(&mut Environment) -> Result<T, ElabError>,
    {
        let snapshot = EnvSnapshot::take(env);
        let backup = env.clone();

        match f(env) {
            Ok(value) => SpeculativeResult::Success(value),
            Err(error) => {
                // Restore the environment to its pre-speculation state.
                *env = backup;
                self.push_snapshot(snapshot.clone());
                SpeculativeResult::Failure { error, snapshot }
            }
        }
    }

    /// Run a closure speculatively, collecting warnings on success.
    ///
    /// Identical to [`speculative`](Self::speculative) but the closure
    /// returns `(T, Vec<String>)`.  If the closure succeeds and the
    /// warning list is non-empty, the result is `SpeculativeResult::Partial`.
    pub(crate) fn speculative_with_warnings<F, T>(
        &mut self,
        env: &mut Environment,
        f: F,
    ) -> SpeculativeResult<T>
    where
        F: FnOnce(&mut Environment) -> Result<(T, Vec<String>), ElabError>,
    {
        let snapshot = EnvSnapshot::take(env);
        let backup = env.clone();

        match f(env) {
            Ok((value, warnings)) => {
                if warnings.is_empty() {
                    SpeculativeResult::Success(value)
                } else {
                    SpeculativeResult::Partial {
                        result: value,
                        warnings,
                    }
                }
            }
            Err(error) => {
                *env = backup;
                self.push_snapshot(snapshot.clone());
                SpeculativeResult::Failure { error, snapshot }
            }
        }
    }
}
