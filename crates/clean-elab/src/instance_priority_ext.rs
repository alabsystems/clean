// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! Extended instance priority resolution with orphan checking and scope filtering.
//!
//! This module builds on [`crate::instance_priority`] to provide:
//!
//! - [`InstancePriorityExt`]: A registry managing extended priority information
//!   including registration, resolution, default instance lookup, and orphan checking.
//! - [`PriorityRule`]: Algebraic encoding of how a priority was assigned (explicit,
//!   default, local, scoped, or derived).
//! - [`InstanceEntry`]: Rich metadata for a registered instance beyond what
//!   [`crate::instances::InstanceInfo`] carries.
//! - [`OrphanError`] / [`OrphanReason`]: Structured error for orphan instance violations.
//!
//! # Orphan Rule
//!
//! Lean 4's orphan rule prevents defining an instance for a class and type that
//! are both foreign to the current module. At least one of the class or the
//! primary type must be defined in `current_module` (or a parent namespace).
//!
//! # Priority Resolution
//!
//! [`compute_effective_priority`] collapses a [`PriorityRule`] to a numeric `u32`
//! priority compatible with [`crate::instance_priority::InstancePriority`].
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Meta/SynthInstance.lean`, `src/Lean/Elab/DeclModifiers.lean`

use clean_kernel::name::Name;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// PriorityRule
// ---------------------------------------------------------------------------

/// How a priority was assigned to an instance.
///
/// The rule is resolved to a numeric priority via [`compute_effective_priority`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PriorityRule {
    /// User-specified numeric priority: `@[instance 500]`.
    Explicit(u32),
    /// Marked `@[default_instance]`; resolved to priority 0.
    Default,
    /// Declared with `@[local instance]`; uses the given base or DEFAULT (100).
    Local,
    /// Visible only when a specific namespace is opened.
    Scoped(Name),
    /// Priority derived from another instance (e.g., superclass projection).
    DerivedFrom(Name),
}

// ---------------------------------------------------------------------------
// InstanceEntry
// ---------------------------------------------------------------------------

/// Rich metadata for a registered instance.
#[derive(Debug, Clone)]
pub(crate) struct InstanceEntry {
    /// Fully qualified instance name.
    pub(crate) name: Name,
    /// Class this instance implements.
    pub(crate) class: Name,
    /// How the priority was assigned.
    pub(crate) priority: PriorityRule,
    /// Whether this is a `@[default_instance]`.
    pub(crate) is_default: bool,
    /// Whether this is a `@[local instance]`.
    pub(crate) is_local: bool,
    /// Module in which the instance was added (if known).
    pub(crate) added_in: Option<Name>,
}

// ---------------------------------------------------------------------------
// OrphanError / OrphanReason
// ---------------------------------------------------------------------------

/// Reason an instance violates the orphan rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OrphanReason {
    /// The class is not defined in the current module.
    ClassNotLocal,
    /// The primary type is not defined in the current module.
    TypeNotLocal,
    /// Neither the class nor the type is local.
    BothNotLocal,
}

impl std::fmt::Display for OrphanReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ClassNotLocal => write!(f, "class is not defined in current module"),
            Self::TypeNotLocal => write!(f, "type is not defined in current module"),
            Self::BothNotLocal => {
                write!(f, "neither class nor type is defined in current module")
            }
        }
    }
}

/// Error returned when an instance violates the orphan rule.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Orphan instance `{instance}` for class `{class}` on type `{type_}`: {reason}")]
pub(crate) struct OrphanError {
    /// Instance that violates the rule.
    pub(crate) instance: Name,
    /// Target class.
    pub(crate) class: Name,
    /// Primary type argument.
    pub(crate) type_: Name,
    /// Why the orphan check failed.
    pub(crate) reason: OrphanReason,
}

// ---------------------------------------------------------------------------
// compute_effective_priority
// ---------------------------------------------------------------------------

/// Default base priority (matches `InstancePriority::DEFAULT` = 100).
const DEFAULT_BASE: u32 = 100;

/// Resolve a [`PriorityRule`] to a numeric priority.
///
/// - `Explicit(n)` → `n`
/// - `Default` → 0 (lowest; tried last as fallback)
/// - `Local` → `base` (typically 100)
/// - `Scoped(_)` → `base`
/// - `DerivedFrom(_)` → `base` (inherits parent's effective priority)
#[must_use]
pub(crate) fn compute_effective_priority(rule: &PriorityRule, base: u32) -> u32 {
    match rule {
        PriorityRule::Explicit(n) => *n,
        PriorityRule::Default => 0,
        PriorityRule::Local | PriorityRule::Scoped(_) | PriorityRule::DerivedFrom(_) => base,
    }
}

// ---------------------------------------------------------------------------
// InstancePriorityExt
// ---------------------------------------------------------------------------

/// Extended instance priority registry.
///
/// Manages [`InstanceEntry`] records keyed by class name, supporting:
/// - Registration with rich priority rules
/// - Priority-sorted candidate resolution
/// - Default instance fallback
/// - Orphan rule checking
/// - Table merging from multiple scopes
#[derive(Debug, Clone, Default)]
pub(crate) struct InstancePriorityExt {
    /// Instances keyed by class name.
    by_class: HashMap<Name, Vec<InstanceEntry>>,
}

impl InstancePriorityExt {
    /// Create an empty registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register an instance.
    pub(crate) fn register_instance(
        &mut self,
        class: &Name,
        inst_name: &Name,
        priority: u32,
        is_default: bool,
        is_local: bool,
    ) {
        let rule = if is_default {
            PriorityRule::Default
        } else if is_local {
            PriorityRule::Local
        } else {
            PriorityRule::Explicit(priority)
        };

        let entry = InstanceEntry {
            name: inst_name.clone(),
            class: class.clone(),
            priority: rule,
            is_default,
            is_local,
            added_in: None,
        };

        self.by_class.entry(class.clone()).or_default().push(entry);
    }

    /// Register an instance with a full [`PriorityRule`] and optional module.
    pub(crate) fn register_entry(&mut self, entry: InstanceEntry) {
        self.by_class
            .entry(entry.class.clone())
            .or_default()
            .push(entry);
    }

    /// Resolve candidates for `class`, returning `(name, effective_priority)` pairs
    /// sorted by priority descending (highest first).
    #[must_use]
    pub(crate) fn resolve_priority(&self, class: &Name, candidates: &[Name]) -> Vec<(Name, u32)> {
        let entries = match self.by_class.get(class) {
            Some(v) => v,
            None => return Vec::new(),
        };

        let mut result: Vec<(Name, u32)> = candidates
            .iter()
            .filter_map(|cand| {
                entries.iter().find(|e| e.name == *cand).map(|e| {
                    let eff = compute_effective_priority(&e.priority, DEFAULT_BASE);
                    (cand.clone(), eff)
                })
            })
            .collect();

        // Sort descending by priority (highest first); stable sort preserves
        // insertion order among equal priorities.
        result.sort_by_key(|b| std::cmp::Reverse(b.1));
        result
    }

    /// Get the default instance for a class, if any.
    ///
    /// When multiple defaults exist, returns the one with the highest effective
    /// priority (which for `Default` rule is 0, so explicit-priority defaults
    /// that were also marked default win).
    #[must_use]
    pub(crate) fn get_default_instance(&self, class: &Name) -> Option<Name> {
        self.by_class
            .get(class)?
            .iter()
            .filter(|e| e.is_default)
            .max_by_key(|e| compute_effective_priority(&e.priority, DEFAULT_BASE))
            .map(|e| e.name.clone())
    }

    /// Check whether `inst_name` violates the orphan rule.
    ///
    /// An instance is orphan if neither `class` nor `type_name` belongs to
    /// `current_module` (using prefix-match: `A.B` is local to `A`).
    pub(crate) fn check_orphan(
        &self,
        inst_name: &Name,
        class: &Name,
        type_name: &Name,
        current_module: &Name,
    ) -> Result<(), OrphanError> {
        let class_local = is_name_local(class, current_module);
        let type_local = is_name_local(type_name, current_module);

        if class_local || type_local {
            return Ok(());
        }

        let reason = OrphanReason::BothNotLocal;
        Err(OrphanError {
            instance: inst_name.clone(),
            class: class.clone(),
            type_: type_name.clone(),
            reason,
        })
    }

    /// Get all entries for a class (unordered).
    #[must_use]
    pub(crate) fn get_entries(&self, class: &Name) -> &[InstanceEntry] {
        self.by_class.get(class).map_or(&[], Vec::as_slice)
    }

    /// Total number of registered entries across all classes.
    #[must_use]
    pub(crate) fn total_entries(&self) -> usize {
        self.by_class.values().map(Vec::len).sum()
    }

    /// Number of classes with at least one registered instance.
    #[must_use]
    pub(crate) fn class_count(&self) -> usize {
        self.by_class.len()
    }
}

// ---------------------------------------------------------------------------
// is_name_local
// ---------------------------------------------------------------------------

/// Check whether `name` is local to `module` via prefix match.
///
/// `Foo.Bar.Baz` is local to `Foo.Bar`, `Foo`, and the anonymous root.
/// The anonymous (empty) root is local to everything.
#[must_use]
fn is_name_local(name: &Name, module: &Name) -> bool {
    // Anonymous module renders as `[anonymous]`, not the empty string,
    // so the historical `module_str.is_empty()` branch never matched.
    // Use `is_anon()` to catch the "root" case correctly.
    if module.is_anon() {
        return true;
    }
    let name_str = name.to_string();
    let module_str = module.to_string();
    name_str == module_str || name_str.starts_with(&format!("{module_str}."))
}

// ---------------------------------------------------------------------------
// merge_instance_tables
// ---------------------------------------------------------------------------

/// Merge multiple [`InstancePriorityExt`] tables into one.
///
/// Entries are combined. If the same instance name appears in multiple tables,
/// all copies are kept (last-writer wins during resolution since
/// `resolve_priority` iterates entries in insertion order and `find` returns
/// the first match).
#[must_use]
pub(crate) fn merge_instance_tables(tables: &[&InstancePriorityExt]) -> InstancePriorityExt {
    let mut merged = InstancePriorityExt::new();
    for table in tables {
        for (class, entries) in &table.by_class {
            let target = merged.by_class.entry(class.clone()).or_default();
            for entry in entries {
                target.push(entry.clone());
            }
        }
    }
    merged
}

// ---------------------------------------------------------------------------
// filter_by_scope
// ---------------------------------------------------------------------------

/// Filter entries to those visible in `current_scope`.
///
/// An entry is visible if:
/// - It is `Local` (always visible within the same compilation unit).
/// - It has `Scoped(ns)` and `current_scope` matches or is a child of `ns`.
/// - It has any other rule (global visibility).
#[must_use]
pub(crate) fn filter_by_scope<'a>(
    instances: &'a [InstanceEntry],
    current_scope: &Name,
) -> Vec<&'a InstanceEntry> {
    instances
        .iter()
        .filter(|e| match &e.priority {
            PriorityRule::Scoped(ns) => is_name_local(current_scope, ns),
            _ => true,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// detect_priority_conflicts
// ---------------------------------------------------------------------------

/// Detect pairs of instances for the same class that have identical effective
/// priority, which can cause non-deterministic resolution order.
///
/// Returns pairs `(a, b)` where `a < b` lexicographically to avoid duplicates.
#[must_use]
pub(crate) fn detect_priority_conflicts(instances: &[InstanceEntry]) -> Vec<(Name, Name)> {
    let mut conflicts = Vec::new();
    for i in 0..instances.len() {
        let pi = compute_effective_priority(&instances[i].priority, DEFAULT_BASE);
        for j in (i + 1)..instances.len() {
            if instances[i].class != instances[j].class {
                continue;
            }
            let pj = compute_effective_priority(&instances[j].priority, DEFAULT_BASE);
            if pi == pj {
                let a = &instances[i].name;
                let b = &instances[j].name;
                // Canonical order to avoid duplicate pairs.
                if a.to_string() <= b.to_string() {
                    conflicts.push((a.clone(), b.clone()));
                } else {
                    conflicts.push((b.clone(), a.clone()));
                }
            }
        }
    }
    conflicts
}
