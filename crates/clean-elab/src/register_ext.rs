// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended declaration registration: batch registration with atomic rollback,
//! pre-registration validation, registration hooks, dependency tracking, and
//! registration statistics/diagnostics.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use clean_kernel::{Environment, Name};

use crate::error::ElabError;
use crate::infer::ElabResult;
use crate::register::register_elab_result;

// =============================================================================
// Error type
// =============================================================================

/// Errors from extended registration operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum RegisterExtError {
    #[error("name conflict: '{0}' already exists in the environment")]
    NameConflict(Name),
    #[error("duplicate name in batch: '{0}' appears more than once")]
    DuplicateInBatch(Name),
    #[error("batch registration failed at index {index}: {source}")]
    BatchFailed {
        index: usize,
        #[source]
        source: ElabError,
    },
    #[error("pre-registration hook rejected declaration '{name}': {reason}")]
    HookRejected { name: String, reason: String },
    #[error("elaboration error: {0}")]
    Elab(#[from] ElabError),
}

// =============================================================================
// Registration statistics
// =============================================================================

/// Statistics collected during a registration session.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct RegistrationStats {
    pub(crate) registered: usize,
    pub(crate) failed: usize,
    pub(crate) conflicts_detected: usize,
    pub(crate) hooks_invoked: usize,
    pub(crate) dependencies_tracked: usize,
    pub(crate) elapsed: Duration,
}

// =============================================================================
// Dependency tracking
// =============================================================================

/// Tracks which declarations depend on which during registration.
#[derive(Debug, Clone, Default)]
pub(crate) struct DependencyTracker {
    /// Map from declaration name to its direct dependencies.
    deps: HashMap<Name, Vec<Name>>,
}

impl DependencyTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            deps: HashMap::new(),
        }
    }

    /// Record that `name` depends on `dependency`.
    pub(crate) fn add_dependency(&mut self, name: Name, dependency: Name) {
        self.deps.entry(name).or_default().push(dependency);
    }

    /// Record multiple dependencies for a declaration.
    pub(crate) fn add_dependencies(&mut self, name: Name, dependencies: Vec<Name>) {
        self.deps.entry(name).or_default().extend(dependencies);
    }

    /// Get the direct dependencies of a declaration.
    #[must_use]
    pub(crate) fn dependencies_of(&self, name: &Name) -> &[Name] {
        self.deps.get(name).map_or(&[], Vec::as_slice)
    }

    /// Get all tracked declaration names.
    #[must_use]
    pub(crate) fn tracked_names(&self) -> Vec<&Name> {
        self.deps.keys().collect()
    }

    /// Total number of dependency edges.
    #[must_use]
    pub(crate) fn edge_count(&self) -> usize {
        self.deps.values().map(Vec::len).sum()
    }

    /// Number of declarations tracked.
    #[must_use]
    pub(crate) fn node_count(&self) -> usize {
        self.deps.len()
    }

    /// Compute the reverse dependency map (dependents of each name).
    #[must_use]
    pub(crate) fn reverse_deps(&self) -> HashMap<Name, Vec<Name>> {
        let mut rev: HashMap<Name, Vec<Name>> = HashMap::new();
        for (name, dep_list) in &self.deps {
            for dep in dep_list {
                rev.entry(dep.clone()).or_default().push(name.clone());
            }
        }
        rev
    }

    /// Clear all tracked dependencies.
    pub(crate) fn clear(&mut self) {
        self.deps.clear();
    }
}

// =============================================================================
// Registration hooks
// =============================================================================

/// A pre-registration hook that validates a declaration before registration.
///
/// Returns `Ok(())` to allow registration, or `Err(reason)` to reject.
pub(crate) type PreRegistrationHook = Box<dyn Fn(&Environment, &ElabResult) -> Result<(), String>>;

/// A post-registration hook invoked after successful registration.
pub(crate) type PostRegistrationHook = Box<dyn Fn(&Environment, &ElabResult)>;

/// Collection of registration hooks for extending the registration pipeline.
#[derive(Default)]
pub(crate) struct RegistrationHooks {
    pre_hooks: Vec<PreRegistrationHook>,
    post_hooks: Vec<PostRegistrationHook>,
}

impl RegistrationHooks {
    /// Create a new empty hook collection.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a pre-registration validation hook.
    pub(crate) fn add_pre_hook(&mut self, hook: PreRegistrationHook) {
        self.pre_hooks.push(hook);
    }

    /// Add a post-registration notification hook.
    pub(crate) fn add_post_hook(&mut self, hook: PostRegistrationHook) {
        self.post_hooks.push(hook);
    }

    /// Number of registered pre-hooks.
    #[must_use]
    pub(crate) fn pre_hook_count(&self) -> usize {
        self.pre_hooks.len()
    }

    /// Number of registered post-hooks.
    #[must_use]
    pub(crate) fn post_hook_count(&self) -> usize {
        self.post_hooks.len()
    }
}

/// Run all pre-registration hooks. Returns number invoked or the first rejection.
fn run_pre_hooks(
    hooks: &[PreRegistrationHook],
    env: &Environment,
    result: &ElabResult,
) -> Result<usize, RegisterExtError> {
    let mut count = 0;
    for hook in hooks {
        hook(env, result).map_err(|reason| {
            let name = result
                .declaration_name()
                .map_or_else(|| "<anonymous>".to_string(), |n| n.to_string());
            RegisterExtError::HookRejected { name, reason }
        })?;
        count += 1;
    }
    Ok(count)
}

/// Run all post-registration hooks. Returns number invoked.
fn run_post_hooks(hooks: &[PostRegistrationHook], env: &Environment, result: &ElabResult) -> usize {
    let mut count = 0;
    for hook in hooks {
        hook(env, result);
        count += 1;
    }
    count
}

// =============================================================================
// Validation
// =============================================================================

/// Validate that a declaration can be registered without name conflicts.
pub(crate) fn validate_no_name_conflict(
    env: &Environment,
    result: &ElabResult,
) -> Result<(), RegisterExtError> {
    if let Some(name) = result.declaration_name() {
        if env.get_const(name).is_some() {
            return Err(RegisterExtError::NameConflict(name.clone()));
        }
    }
    Ok(())
}

/// Validate that no two results in a batch share the same name.
pub(crate) fn validate_batch_no_duplicates(results: &[ElabResult]) -> Result<(), RegisterExtError> {
    let mut seen = HashMap::new();
    for (idx, result) in results.iter().enumerate() {
        if let Some(name) = result.declaration_name() {
            if let Some(_prev_idx) = seen.insert(name.clone(), idx) {
                return Err(RegisterExtError::DuplicateInBatch(name.clone()));
            }
        }
    }
    Ok(())
}

/// Validate an entire batch: inter-batch duplicates and env conflicts.
pub(crate) fn validate_batch(
    env: &Environment,
    results: &[ElabResult],
) -> Result<usize, RegisterExtError> {
    validate_batch_no_duplicates(results)?;
    let mut conflicts = 0;
    for result in results {
        if let Err(RegisterExtError::NameConflict(_)) = validate_no_name_conflict(env, result) {
            conflicts += 1;
        }
    }
    Ok(conflicts)
}

// =============================================================================
// Batch registration
// =============================================================================

/// Register multiple elaboration results atomically.
///
/// Clones the environment, registers all results into the clone, and on
/// success swaps the clone into the original. On failure, the original
/// environment is untouched.
pub(crate) fn register_batch(
    env: &mut Environment,
    results: &[ElabResult],
) -> Result<RegistrationStats, RegisterExtError> {
    register_batch_with_hooks(env, results, &RegistrationHooks::new())
}

/// Register multiple elaboration results atomically with hooks.
pub(crate) fn register_batch_with_hooks(
    env: &mut Environment,
    results: &[ElabResult],
    hooks: &RegistrationHooks,
) -> Result<RegistrationStats, RegisterExtError> {
    let start = Instant::now();
    let mut stats = RegistrationStats::default();

    if results.is_empty() {
        stats.elapsed = start.elapsed();
        return Ok(stats);
    }

    validate_batch_no_duplicates(results)?;
    let mut env_clone = env.clone();

    for (index, result) in results.iter().enumerate() {
        let hook_count = run_pre_hooks(&hooks.pre_hooks, &env_clone, result)?;
        stats.hooks_invoked += hook_count;

        match register_elab_result(&mut env_clone, result) {
            Ok(()) => {
                stats.registered += 1;
                let post_count = run_post_hooks(&hooks.post_hooks, &env_clone, result);
                stats.hooks_invoked += post_count;
            }
            Err(e) => {
                return Err(RegisterExtError::BatchFailed { index, source: e });
            }
        }
    }

    *env = env_clone;
    stats.elapsed = start.elapsed();
    Ok(stats)
}

// =============================================================================
// Hooked single registration
// =============================================================================

/// Register a single elaboration result with hooks and dependency tracking.
pub(crate) fn register_with_hooks(
    env: &mut Environment,
    result: &ElabResult,
    hooks: &RegistrationHooks,
    tracker: Option<&mut DependencyTracker>,
) -> Result<RegistrationStats, RegisterExtError> {
    let start = Instant::now();
    let mut stats = RegistrationStats::default();

    let hook_count = run_pre_hooks(&hooks.pre_hooks, env, result)?;
    stats.hooks_invoked += hook_count;

    register_elab_result(env, result)?;
    stats.registered += 1;

    if let Some(tracker) = tracker {
        if let Some(name) = result.declaration_name() {
            tracker.add_dependencies(name.clone(), Vec::new());
            stats.dependencies_tracked += 1;
        }
    }

    let post_count = run_post_hooks(&hooks.post_hooks, env, result);
    stats.hooks_invoked += post_count;

    stats.elapsed = start.elapsed();
    Ok(stats)
}

// =============================================================================
// Batch result with diagnostics
// =============================================================================

/// Result of a batch registration including per-item diagnostics.
#[derive(Debug, Clone)]
pub(crate) struct BatchResult {
    pub(crate) stats: RegistrationStats,
    pub(crate) registered_names: Vec<Name>,
    pub(crate) tracker: DependencyTracker,
}

/// Register a batch with full diagnostics.
pub(crate) fn register_batch_full(
    env: &mut Environment,
    results: &[ElabResult],
    hooks: &RegistrationHooks,
) -> Result<BatchResult, RegisterExtError> {
    let start = Instant::now();
    let mut stats = RegistrationStats::default();
    let mut tracker = DependencyTracker::new();
    let mut registered_names = Vec::new();

    if results.is_empty() {
        stats.elapsed = start.elapsed();
        return Ok(BatchResult {
            stats,
            registered_names,
            tracker,
        });
    }

    validate_batch_no_duplicates(results)?;
    let mut env_clone = env.clone();

    for (index, result) in results.iter().enumerate() {
        let hook_count = run_pre_hooks(&hooks.pre_hooks, &env_clone, result)?;
        stats.hooks_invoked += hook_count;

        match register_elab_result(&mut env_clone, result) {
            Ok(()) => {
                stats.registered += 1;
                if let Some(name) = result.declaration_name() {
                    registered_names.push(name.clone());
                    tracker.add_dependencies(name.clone(), Vec::new());
                    stats.dependencies_tracked += 1;
                }
                let post_count = run_post_hooks(&hooks.post_hooks, &env_clone, result);
                stats.hooks_invoked += post_count;
            }
            Err(e) => {
                return Err(RegisterExtError::BatchFailed { index, source: e });
            }
        }
    }

    *env = env_clone;
    stats.elapsed = start.elapsed();
    Ok(BatchResult {
        stats,
        registered_names,
        tracker,
    })
}

// =============================================================================
// Convenience helpers
// =============================================================================

/// Merge two stats structs (e.g., from sequential batch runs).
#[must_use]
pub(crate) fn merge_stats(a: &RegistrationStats, b: &RegistrationStats) -> RegistrationStats {
    RegistrationStats {
        registered: a.registered + b.registered,
        failed: a.failed + b.failed,
        conflicts_detected: a.conflicts_detected + b.conflicts_detected,
        hooks_invoked: a.hooks_invoked + b.hooks_invoked,
        dependencies_tracked: a.dependencies_tracked + b.dependencies_tracked,
        elapsed: a.elapsed + b.elapsed,
    }
}

/// Check if a name would conflict with an existing constant.
#[must_use]
pub(crate) fn has_name_conflict(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
}
