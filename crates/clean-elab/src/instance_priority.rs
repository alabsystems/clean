// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance priority management with scoping and backtracking.
//!
//! This module enhances the type class instance resolution system with:
//!
//! - [`InstancePriority`]: A typed wrapper for instance priority values, providing
//!   ordered comparison and standard priority levels.
//! - [`PriorityQueue`]: A sorted collection of instance candidates that maintains
//!   priority ordering for efficient search.
//! - [`ScopedInstances`]: Section-local instance registration with RAII-style
//!   push/pop scoping semantics.
//! - [`DefaultInstanceFallback`]: Fallback resolution using `@[default_instance]`
//!   when no regular instance matches.
//!
//! # Priority Model (Lean 4 compatible)
//!
//! Higher numeric priority = tried first. This matches Lean 4's convention
//! where `@[instance 1000]` overrides the default priority of 100.
//!
//! Priority tiers:
//! - `InstancePriority::OVERRIDE` (1000): User-specified high priority
//! - `InstancePriority::HIGH` (500): Common high-priority instances
//! - `InstancePriority::DEFAULT` (100): Standard priority for undecorated instances
//! - `InstancePriority::LOW` (50): Explicitly low-priority instances
//! - `InstancePriority::DEFAULT_INSTANCE` (0): `@[default_instance]` fallback
//!
//! # Scoping
//!
//! Instance visibility follows Lean 4's attribute scoping:
//! - **Global**: Visible everywhere the declaring module is imported.
//! - **Scoped**: Visible only when the declaring namespace is opened.
//! - **Local**: Visible only in the current section/file.
//!
//! [`ScopedInstances`] manages a stack of local instance scopes,
//! each containing instances registered in that scope. When a scope is
//! popped, its instances are removed from resolution.
//!
//! # Backtracking
//!
//! When multiple instances match, the system tries them in priority order
//! (highest first). If a higher-priority instance fails during unification
//! or recursive instance resolution, the engine backtracks and tries the
//! next candidate. Default instances are tried last as a fallback.
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Meta/SynthInstance.lean`, `src/Lean/Attributes.lean`

use crate::instances::{InstanceInfo, InstanceTable};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

// ---------------------------------------------------------------------------
// InstancePriority newtype
// ---------------------------------------------------------------------------

/// Typed wrapper for instance priority values.
///
/// Higher values indicate higher priority (tried first during resolution).
/// This follows Lean 4's convention where `@[instance 1000]` takes precedence
/// over `@[instance 100]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct InstancePriority(pub u32);

impl InstancePriority {
    /// Priority for `@[default_instance]` fallback (lowest).
    pub(crate) const DEFAULT_INSTANCE: Self = Self(0);

    /// Explicitly low priority (e.g., `@[instance 50]`).
    pub(crate) const LOW: Self = Self(50);

    /// Standard priority for undecorated `instance` declarations.
    /// Matches `DEFAULT_PRIORITY` in `instances.rs`.
    pub(crate) const DEFAULT: Self = Self(100);

    /// High priority for commonly needed instances.
    pub(crate) const HIGH: Self = Self(500);

    /// Override priority for user-specified high-priority instances.
    pub(crate) const OVERRIDE: Self = Self(1000);

    /// Create a priority from a raw u32 value.
    #[must_use]
    pub(crate) fn new(value: u32) -> Self {
        Self(value)
    }

    /// Get the raw numeric value.
    #[must_use]
    pub(crate) fn value(self) -> u32 {
        self.0
    }

    /// Check if this priority is a default-instance fallback.
    #[must_use]
    pub(crate) fn is_default_instance(self) -> bool {
        self == Self::DEFAULT_INSTANCE
    }
}

impl PartialOrd for InstancePriority {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for InstancePriority {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Higher value = higher priority = Greater
        self.0.cmp(&other.0)
    }
}

impl Default for InstancePriority {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl From<u32> for InstancePriority {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

impl From<InstancePriority> for u32 {
    fn from(priority: InstancePriority) -> Self {
        priority.0
    }
}

// ---------------------------------------------------------------------------
// PriorityQueue
// ---------------------------------------------------------------------------

/// A candidate instance with its resolved priority.
#[derive(Debug, Clone)]
pub(crate) struct PrioritizedInstance {
    /// The instance information.
    pub(crate) info: InstanceInfo,
    /// The resolved priority (may differ from `info.priority` for default instances).
    pub(crate) priority: InstancePriority,
    /// Whether this is a default-instance fallback.
    pub(crate) is_default: bool,
}

/// A sorted collection of instance candidates maintaining priority order.
///
/// Instances are stored in descending priority order (highest priority first).
/// This is the order in which they should be tried during resolution.
///
/// The queue distinguishes between regular instances and default-instance
/// fallbacks. Regular instances are always tried before default instances,
/// regardless of numeric priority.
#[derive(Debug, Clone, Default)]
pub(crate) struct PriorityQueue {
    /// Regular instances sorted by priority (highest first).
    regular: Vec<PrioritizedInstance>,
    /// Default instances sorted by priority (highest first).
    /// These are tried only when no regular instance matches.
    defaults: Vec<PrioritizedInstance>,
}

impl PriorityQueue {
    /// Create an empty priority queue.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Insert an instance into the queue at the correct position.
    pub(crate) fn insert(&mut self, info: InstanceInfo, is_default: bool) {
        let priority = InstancePriority::new(info.priority);
        let entry = PrioritizedInstance {
            info,
            priority,
            is_default,
        };

        let target = if is_default {
            &mut self.defaults
        } else {
            &mut self.regular
        };

        // Binary search for insertion point (maintain descending order)
        let pos = target.partition_point(|existing| existing.priority >= priority);
        target.insert(pos, entry);
    }

    /// Iterate over all candidates in resolution order.
    ///
    /// Regular instances are yielded first (highest priority first),
    /// followed by default instances (highest priority first).
    pub(crate) fn iter(&self) -> impl Iterator<Item = &PrioritizedInstance> {
        self.regular.iter().chain(self.defaults.iter())
    }

    /// Total number of candidates (regular + default).
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.regular.len() + self.defaults.len()
    }

    /// Check if the queue is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.regular.is_empty() && self.defaults.is_empty()
    }

    /// Number of regular (non-default) instances.
    #[must_use]
    pub(crate) fn regular_count(&self) -> usize {
        self.regular.len()
    }

    /// Number of default-instance fallbacks.
    #[must_use]
    pub(crate) fn default_count(&self) -> usize {
        self.defaults.len()
    }
}

// ---------------------------------------------------------------------------
// ScopedInstances
// ---------------------------------------------------------------------------

/// A single scope frame containing instances registered in that scope.
#[derive(Debug, Clone, Default)]
struct ScopeFrame {
    /// Instances registered in this scope, keyed by class name.
    instances: Vec<ScopedInstanceEntry>,
}

/// An instance registered in a local/scoped context.
#[derive(Debug, Clone)]
pub(crate) struct ScopedInstanceEntry {
    /// Name of the instance.
    pub(crate) name: Name,
    /// Name of the class this instance implements.
    pub(crate) class_name: Name,
    /// The instance expression.
    pub(crate) expr: Expr,
    /// The instance type.
    pub(crate) type_: Expr,
    /// Priority.
    pub(crate) priority: InstancePriority,
}

/// Section-local instance registration with push/pop scoping.
///
/// Manages a stack of scopes, each containing instance registrations
/// that are only visible within that scope. When a scope is popped,
/// its instances are removed from resolution.
///
/// This models Lean 4's `@[local instance]` and section-level instance
/// declarations that are not visible outside their declaring section.
///
/// # Example (conceptual)
///
/// ```text
/// scoped.push_scope();
/// scoped.register_local(instance_info);
/// // ... instance is visible during resolution ...
/// scoped.pop_scope();
/// // ... instance is no longer visible ...
/// ```
#[derive(Debug, Clone, Default)]
pub(crate) struct ScopedInstances {
    /// Stack of scope frames. The last entry is the innermost scope.
    scopes: Vec<ScopeFrame>,
}

impl ScopedInstances {
    /// Create an empty scoped-instance manager with no active scopes.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Push a new scope frame.
    ///
    /// Instances registered after this call will belong to the new scope
    /// and will be removed when [`pop_scope`](Self::pop_scope) is called.
    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(ScopeFrame::default());
    }

    /// Pop the innermost scope frame, removing all instances registered in it.
    ///
    /// Returns `true` if a scope was popped, `false` if no scopes were active.
    pub(crate) fn pop_scope(&mut self) -> bool {
        self.scopes.pop().is_some()
    }

    /// Register an instance in the current innermost scope.
    ///
    /// If no scope is active, the instance is silently dropped. Callers should
    /// ensure a scope has been pushed before registering.
    pub(crate) fn register_local(
        &mut self,
        name: Name,
        class_name: Name,
        expr: Expr,
        type_: Expr,
        priority: InstancePriority,
    ) {
        if let Some(frame) = self.scopes.last_mut() {
            frame.instances.push(ScopedInstanceEntry {
                name,
                class_name,
                expr,
                type_,
                priority,
            });
        }
    }

    /// Get all visible instances for a given class across all active scopes.
    ///
    /// Returns instances from all scope frames (innermost first) that match
    /// the given class name, sorted by priority (highest first).
    #[must_use]
    pub(crate) fn get_instances(&self, class_name: &Name) -> Vec<&ScopedInstanceEntry> {
        let mut result: Vec<&ScopedInstanceEntry> = self
            .scopes
            .iter()
            .rev()
            .flat_map(|frame| {
                frame
                    .instances
                    .iter()
                    .filter(|entry| entry.class_name == *class_name)
            })
            .collect();

        // Sort by priority descending (highest first)
        result.sort_by_key(|b| std::cmp::Reverse(b.priority));
        result
    }

    /// Check whether any scope has instances for the given class.
    #[must_use]
    pub(crate) fn has_instances(&self, class_name: &Name) -> bool {
        self.scopes.iter().any(|frame| {
            frame
                .instances
                .iter()
                .any(|entry| entry.class_name == *class_name)
        })
    }

    /// Current scope depth (number of active scope frames).
    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// Total number of registered instances across all scopes.
    #[must_use]
    pub(crate) fn total_instances(&self) -> usize {
        self.scopes.iter().map(|frame| frame.instances.len()).sum()
    }
}

// ---------------------------------------------------------------------------
// DefaultInstanceFallback
// ---------------------------------------------------------------------------

/// Manages default-instance fallback resolution.
///
/// When no regular instance matches during resolution, the system consults
/// default instances as a fallback. This handles `@[default_instance]`
/// declarations in Lean 4.
///
/// Default instances are tracked separately from regular instances so they
/// can be tried with lower priority regardless of their numeric priority
/// value.
#[derive(Debug, Clone, Default)]
pub(crate) struct DefaultInstanceFallback {
    /// Default instances keyed by class name.
    defaults: std::collections::HashMap<Name, Vec<DefaultInstanceEntry>>,
}

/// A registered default instance.
#[derive(Debug, Clone)]
pub(crate) struct DefaultInstanceEntry {
    /// Name of the default instance declaration.
    pub(crate) name: Name,
    /// The instance expression.
    pub(crate) expr: Expr,
    /// The instance type.
    pub(crate) type_: Expr,
    /// Priority among default instances (higher = tried first).
    pub(crate) priority: InstancePriority,
}

impl DefaultInstanceFallback {
    /// Create an empty default-instance manager.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a default instance for a class.
    pub(crate) fn register(
        &mut self,
        class_name: Name,
        name: Name,
        expr: Expr,
        type_: Expr,
        priority: InstancePriority,
    ) {
        let entries = self.defaults.entry(class_name).or_default();
        let entry = DefaultInstanceEntry {
            name,
            expr,
            type_,
            priority,
        };

        // Insert maintaining descending priority order
        let pos = entries.partition_point(|e| e.priority >= priority);
        entries.insert(pos, entry);
    }

    /// Get default instances for a class, sorted by priority (highest first).
    #[must_use]
    pub(crate) fn get_defaults(&self, class_name: &Name) -> &[DefaultInstanceEntry] {
        self.defaults.get(class_name).map_or(&[], Vec::as_slice)
    }

    /// Check if any default instances exist for a class.
    #[must_use]
    pub(crate) fn has_defaults(&self, class_name: &Name) -> bool {
        self.defaults.get(class_name).is_some_and(|v| !v.is_empty())
    }

    /// Total number of registered default instances.
    #[must_use]
    pub(crate) fn total_defaults(&self) -> usize {
        self.defaults.values().map(Vec::len).sum()
    }
}

// ---------------------------------------------------------------------------
// Helper: build a PriorityQueue from an InstanceTable + defaults
// ---------------------------------------------------------------------------

/// Build a [`PriorityQueue`] for a class from the global instance table and
/// default instance fallback registry.
///
/// This merges regular instances from the `InstanceTable` with default
/// instances from the `DefaultInstanceFallback`, maintaining proper ordering:
/// regular instances are tried before defaults.
#[must_use]
pub(crate) fn build_priority_queue(
    class_name: &Name,
    table: &InstanceTable,
    defaults: &DefaultInstanceFallback,
) -> PriorityQueue {
    let mut queue = PriorityQueue::new();

    // Add regular instances from the global table
    for inst in table.get_instances(class_name) {
        queue.insert(inst.clone(), false);
    }

    // Add default instances
    for default in defaults.get_defaults(class_name) {
        let info = InstanceInfo {
            name: default.name.clone(),
            class_name: class_name.clone(),
            expr: default.expr.clone(),
            type_: default.type_.clone(),
            priority: default.priority.value(),
            synth_order: None,
        };
        queue.insert(info, true);
    }

    queue
}

#[cfg(test)]
#[path = "instance_priority_tests.rs"]
mod tests;
