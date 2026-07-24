// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute scoping for `@[scoped]`, `@[local]`, and `@[export]` modifiers.
//!
//! In Lean 4, attributes can have three visibility scopes:
//!
//! - **Global** (`@[simp]`): The attribute effect is visible everywhere the
//!   declaration is imported.
//! - **Scoped** (`@[scoped simp]`): The attribute effect is only active when
//!   the declaring namespace is opened via `open`.
//! - **Local** (`@[local simp]`): The attribute effect is only active in the
//!   current section or file.
//!
//! This module provides the [`ScopedAttrRegistry`] which tracks scoped
//! attribute registrations and resolves which entries are active given
//! the set of currently opened namespaces.
//!
//! Reference: Lean 4 `src/Lean/Attributes.lean`, `AttributeKind` enum.

use clean_kernel::name::Name;
use std::collections::{HashMap, HashSet};

/// The visibility scope of an attribute registration.
///
/// Controls when the attribute's effect is active during elaboration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum AttributeScope {
    /// Visible everywhere the declaration is imported (default).
    #[default]
    Global,
    /// Visible only when the given namespace is opened via `open`.
    Scoped(Name),
    /// Visible only in the current section or file.
    Local,
}

/// A single scoped attribute registration.
///
/// Associates a declaration with an attribute name under a specific scope
/// and namespace context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedAttrEntry {
    /// Name of the declaration carrying the attribute.
    pub decl_name: Name,
    /// Name of the attribute (e.g. `"simp"`, `"instance"`).
    pub attr_name: String,
    /// Visibility scope of this registration.
    pub scope: AttributeScope,
    /// Namespace in which the attribute was declared.
    pub namespace: Name,
}

/// Registry for scoped attribute entries.
///
/// Maintains a collection of [`ScopedAttrEntry`] values indexed by attribute
/// name, along with the set of currently opened namespaces. Queries like
/// [`get_active`](ScopedAttrRegistry::get_active) filter entries based on
/// scope visibility rules.
#[derive(Debug, Clone, Default)]
pub struct ScopedAttrRegistry {
    /// Entries indexed by attribute name for efficient lookup.
    entries: HashMap<String, Vec<ScopedAttrEntry>>,
    /// The set of namespaces currently opened via `open`.
    open_namespaces: HashSet<Name>,
}

impl ScopedAttrRegistry {
    /// Create an empty registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a scoped attribute entry.
    ///
    /// The entry is indexed by its `attr_name` for efficient lookup.
    pub(crate) fn register(&mut self, entry: ScopedAttrEntry) {
        self.entries
            .entry(entry.attr_name.clone())
            .or_default()
            .push(entry);
    }

    /// Return all entries for the given attribute that are currently visible.
    ///
    /// Visibility is determined by the entry's scope and the set of
    /// currently opened namespaces:
    /// - `Global` entries are always visible.
    /// - `Scoped(ns)` entries are visible only if `ns` is in the open set.
    /// - `Local` entries are always visible (file/section filtering is the
    ///   caller's responsibility).
    #[must_use]
    pub(crate) fn get_active(&self, attr_name: &str) -> Vec<&ScopedAttrEntry> {
        self.entries
            .get(attr_name)
            .map(|entries| {
                entries
                    .iter()
                    .filter(|e| is_visible(e, &self.open_namespaces))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Mark a namespace as opened, making its `Scoped` entries visible.
    pub(crate) fn open_namespace(&mut self, ns: &Name) {
        self.open_namespaces.insert(ns.clone());
    }

    /// Mark a namespace as closed, hiding its `Scoped` entries.
    pub(crate) fn close_namespace(&mut self, ns: &Name) {
        self.open_namespaces.remove(ns);
    }

    /// Return all entries for the given attribute regardless of scope.
    ///
    /// Returns an empty slice if no entries exist for the attribute.
    #[must_use]
    pub(crate) fn get_all(&self, attr_name: &str) -> &[ScopedAttrEntry] {
        self.entries.get(attr_name).map_or(&[], Vec::as_slice)
    }

    /// Return the set of currently opened namespaces.
    #[must_use]
    pub(crate) fn open_namespaces(&self) -> &HashSet<Name> {
        &self.open_namespaces
    }

    /// Check whether the registry contains any entries.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Total number of registered entries across all attributes.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }

    /// Iterate over all entry lists (one per attribute name).
    ///
    /// Each item is a slice of entries registered under a single attribute name.
    pub(crate) fn entries(&self) -> impl Iterator<Item = &Vec<ScopedAttrEntry>> {
        self.entries.values()
    }
}

/// Check whether a scoped attribute entry is visible given the set of
/// currently opened namespaces.
///
/// - `Global`: always visible.
/// - `Scoped(ns)`: visible only if `ns` is in `open_namespaces`.
/// - `Local`: always visible (section/file scoping is the caller's job).
#[must_use]
pub(crate) fn is_visible(entry: &ScopedAttrEntry, open_namespaces: &HashSet<Name>) -> bool {
    match &entry.scope {
        AttributeScope::Global => true,
        AttributeScope::Scoped(ns) => open_namespaces.contains(ns),
        AttributeScope::Local => true,
    }
}
