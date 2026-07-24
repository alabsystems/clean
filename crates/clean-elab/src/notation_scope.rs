// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Notation scoping and precedence-aware resolution for Lean 5.
//!
//! In Lean 4, notations can be scoped to namespaces and have numeric
//! priorities that control binding strength. When multiple notations
//! match the same token, the one with the highest priority wins.
//! Scoped notations are only active when their declaring namespace is
//! opened via `open`.
//!
//! # Architecture
//!
//! [`NotationScopeEntry`] represents a single notation with its priority,
//! namespace binding, and expansion template. [`NotationScopeRegistry`]
//! stores entries indexed by token and provides scope-aware resolution:
//!
//! - **Global** notations (namespace = `None`) are always visible.
//! - **Scoped** notations (namespace = `Some(ns)`) are visible only when
//!   `ns` is in the set of open namespaces.
//! - **Local** notations are visible only in the current section/file.
//!
//! Resolution returns entries filtered by visibility and sorted by
//! descending priority (highest first).
//!
//! # Lean 4 Reference
//!
//! See `src/Lean/Parser/Extension.lean` for notation registration and
//! `src/Lean/Elab/Notation.lean` for scoped notation elaboration.

use std::collections::{HashMap, HashSet};

/// The kind of notation (syntactic shape).
///
/// Extends the parser's `NotationKind` with `Macro` for macro-based
/// notations that are expanded before parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ScopedNotationKind {
    /// Prefix operator (e.g., `- x`, `! x`).
    Prefix,
    /// Infix operator (e.g., `x + y`).
    Infix,
    /// Postfix operator (e.g., `x?`).
    Postfix,
    /// General notation command (arbitrary mixfix).
    Notation,
    /// Macro notation (expanded before parsing).
    Macro,
}

impl std::fmt::Display for ScopedNotationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prefix => write!(f, "prefix"),
            Self::Infix => write!(f, "infix"),
            Self::Postfix => write!(f, "postfix"),
            Self::Notation => write!(f, "notation"),
            Self::Macro => write!(f, "macro"),
        }
    }
}

/// A notation entry with priority and namespace binding.
///
/// Each entry associates a token with an expansion template, a numeric
/// priority for disambiguation, and an optional namespace scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotationScopeEntry {
    /// Notation name/token (e.g., `"+"`).
    pub(crate) name: String,
    /// The syntactic kind of this notation.
    pub(crate) kind: ScopedNotationKind,
    /// Precedence level: higher values bind tighter.
    pub(crate) priority: u32,
    /// Namespace scope: `None` = global, `Some(ns)` = scoped to `ns`.
    pub(crate) namespace: Option<String>,
    /// The expansion template string.
    pub(crate) expansion: String,
    /// Whether this notation is local to the current section/file.
    pub(crate) is_local: bool,
}

impl NotationScopeEntry {
    /// Create a new notation entry.
    #[must_use]
    pub(crate) fn new(
        name: &str,
        kind: ScopedNotationKind,
        priority: u32,
        namespace: Option<&str>,
        expansion: &str,
        is_local: bool,
    ) -> Self {
        Self {
            name: name.to_owned(),
            kind,
            priority,
            namespace: namespace.map(str::to_owned),
            expansion: expansion.to_owned(),
            is_local,
        }
    }

    /// Create a global notation entry (visible everywhere).
    #[must_use]
    pub(crate) fn global(
        name: &str,
        kind: ScopedNotationKind,
        priority: u32,
        expansion: &str,
    ) -> Self {
        Self::new(name, kind, priority, None, expansion, false)
    }

    /// Create a scoped notation entry (visible when namespace is open).
    #[must_use]
    pub(crate) fn scoped(
        name: &str,
        kind: ScopedNotationKind,
        priority: u32,
        namespace: &str,
        expansion: &str,
    ) -> Self {
        Self::new(name, kind, priority, Some(namespace), expansion, false)
    }

    /// Create a local notation entry (visible in current section only).
    #[must_use]
    pub(crate) fn local(
        name: &str,
        kind: ScopedNotationKind,
        priority: u32,
        expansion: &str,
    ) -> Self {
        Self::new(name, kind, priority, None, expansion, true)
    }

    /// The notation name/token.
    #[must_use]
    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    /// The notation kind.
    #[must_use]
    pub(crate) fn kind(&self) -> ScopedNotationKind {
        self.kind
    }

    /// The precedence level.
    #[must_use]
    pub(crate) fn priority(&self) -> u32 {
        self.priority
    }

    /// The namespace scope, if any.
    #[must_use]
    pub(crate) fn namespace(&self) -> Option<&str> {
        self.namespace.as_deref()
    }

    /// The expansion template.
    #[must_use]
    pub(crate) fn expansion(&self) -> &str {
        &self.expansion
    }

    /// Whether this notation is local to the current section/file.
    #[must_use]
    pub(crate) fn is_local(&self) -> bool {
        self.is_local
    }

    /// Whether this notation is global (not scoped, not local).
    #[must_use]
    pub(crate) fn is_global(&self) -> bool {
        self.namespace.is_none() && !self.is_local
    }

    /// Whether this entry is visible given the set of open namespaces.
    ///
    /// Visibility rules:
    /// - Global entries are always visible.
    /// - Scoped entries are visible when their namespace is in `open_ns`.
    /// - Local entries are always visible (lifetime managed by section scope).
    #[must_use]
    pub(crate) fn is_visible(&self, open_ns: &HashSet<String>) -> bool {
        match &self.namespace {
            None => true, // global or local — always visible
            Some(ns) => open_ns.contains(ns),
        }
    }
}

/// Registry of notation entries with scope-aware resolution.
///
/// Entries are indexed by their notation token for O(1) lookup. Each
/// token bucket is maintained in descending priority order (highest first).
///
/// The registry tracks the set of currently open namespaces. Resolution
/// methods filter entries by visibility (global + matching scoped) and
/// return them in priority order.
///
/// # Example
///
/// ```text
/// let mut reg = NotationScopeRegistry::new();
/// reg.register(NotationScopeEntry::global("+", Infix, 65, "HAdd.hAdd"));
/// reg.register(NotationScopeEntry::scoped("+", Infix, 70, "Nat", "Nat.add"));
///
/// // Before opening Nat: only global entry visible
/// assert_eq!(reg.resolve("+").expect("global").expansion(), "HAdd.hAdd");
///
/// // After opening Nat: scoped entry wins (higher priority)
/// reg.open_namespace("Nat");
/// assert_eq!(reg.resolve("+").expect("scoped").expansion(), "Nat.add");
/// ```
pub(crate) struct NotationScopeRegistry {
    /// Entries indexed by notation token. Within each bucket, entries
    /// are sorted by descending priority (highest first).
    entries: HashMap<String, Vec<NotationScopeEntry>>,
    /// Currently opened namespaces.
    open_namespaces: HashSet<String>,
}

impl std::fmt::Debug for NotationScopeRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NotationScopeRegistry")
            .field("token_count", &self.entries.len())
            .field("open_namespaces", &self.open_namespaces)
            .finish()
    }
}

impl Default for NotationScopeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl NotationScopeRegistry {
    /// Create a new empty notation scope registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            entries: HashMap::new(),
            open_namespaces: HashSet::new(),
        }
    }

    /// Register a notation entry.
    ///
    /// The entry is indexed by its name (token). Within each token bucket,
    /// entries are maintained in descending priority order. Entries with
    /// equal priority preserve insertion order (stable sort).
    pub(crate) fn register(&mut self, entry: NotationScopeEntry) {
        let bucket = self.entries.entry(entry.name.clone()).or_default();
        let pos = bucket
            .iter()
            .position(|e| e.priority < entry.priority)
            .unwrap_or(bucket.len());
        bucket.insert(pos, entry);
    }

    /// Open a namespace, making its scoped notations visible.
    ///
    /// Idempotent: opening an already-open namespace is a no-op.
    pub(crate) fn open_namespace(&mut self, ns: &str) {
        self.open_namespaces.insert(ns.to_owned());
    }

    /// Close a namespace, hiding its scoped notations.
    ///
    /// Idempotent: closing an already-closed namespace is a no-op.
    pub(crate) fn close_namespace(&mut self, ns: &str) {
        self.open_namespaces.remove(ns);
    }

    /// Check whether a namespace is currently open.
    #[must_use]
    pub(crate) fn is_namespace_open(&self, ns: &str) -> bool {
        self.open_namespaces.contains(ns)
    }

    /// Get the set of currently open namespaces.
    #[must_use]
    pub(crate) fn open_namespaces(&self) -> &HashSet<String> {
        &self.open_namespaces
    }

    /// Resolve the best-matching notation for a token.
    ///
    /// Returns the highest-priority entry that is visible given the
    /// current set of open namespaces, or `None` if no entry matches.
    #[must_use]
    pub(crate) fn resolve(&self, token: &str) -> Option<&NotationScopeEntry> {
        self.entries
            .get(token)?
            .iter()
            .find(|e| e.is_visible(&self.open_namespaces))
    }

    /// Resolve the best-matching notation using an explicit set of
    /// open namespaces (overriding the registry's tracked state).
    ///
    /// Useful when the caller has its own namespace tracking.
    #[must_use]
    pub(crate) fn resolve_with_namespaces(
        &self,
        token: &str,
        open_ns: &[String],
    ) -> Option<&NotationScopeEntry> {
        let ns_set: HashSet<String> = open_ns.iter().cloned().collect();
        self.entries
            .get(token)?
            .iter()
            .find(|e| e.is_visible(&ns_set))
    }

    /// Resolve all matching notations for a token, sorted by descending priority.
    ///
    /// Returns all visible entries (global + matching scoped), in
    /// priority order (highest first).
    #[must_use]
    pub(crate) fn resolve_all(&self, token: &str) -> Vec<&NotationScopeEntry> {
        self.entries
            .get(token)
            .map(|bucket| {
                bucket
                    .iter()
                    .filter(|e| e.is_visible(&self.open_namespaces))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Resolve all matching notations using an explicit set of open namespaces.
    #[must_use]
    pub(crate) fn resolve_all_with_namespaces(
        &self,
        token: &str,
        open_ns: &[String],
    ) -> Vec<&NotationScopeEntry> {
        let ns_set: HashSet<String> = open_ns.iter().cloned().collect();
        self.entries
            .get(token)
            .map(|bucket| bucket.iter().filter(|e| e.is_visible(&ns_set)).collect())
            .unwrap_or_default()
    }

    /// Get all entries scoped to a specific namespace.
    ///
    /// Returns entries in their registered order (descending priority
    /// within each token, but across tokens the order is unspecified).
    #[must_use]
    pub(crate) fn scoped_entries(&self, ns: &str) -> Vec<&NotationScopeEntry> {
        self.entries
            .values()
            .flat_map(|bucket| bucket.iter())
            .filter(|e| e.namespace.as_deref() == Some(ns))
            .collect()
    }

    /// Get all global entries (not scoped to any namespace, not local).
    #[must_use]
    pub(crate) fn global_entries(&self) -> Vec<&NotationScopeEntry> {
        self.entries
            .values()
            .flat_map(|bucket| bucket.iter())
            .filter(|e| e.is_global())
            .collect()
    }

    /// Get all local entries.
    #[must_use]
    pub(crate) fn local_entries(&self) -> Vec<&NotationScopeEntry> {
        self.entries
            .values()
            .flat_map(|bucket| bucket.iter())
            .filter(|e| e.is_local)
            .collect()
    }

    /// Remove all local notation entries.
    ///
    /// Called when exiting a section/file scope to clean up local notations.
    pub(crate) fn clear_local_entries(&mut self) {
        for bucket in self.entries.values_mut() {
            bucket.retain(|e| !e.is_local);
        }
        // Remove empty buckets to keep the map clean
        self.entries.retain(|_, bucket| !bucket.is_empty());
    }

    /// Check whether any notation is registered for a token.
    #[must_use]
    pub(crate) fn has_notation(&self, token: &str) -> bool {
        self.entries
            .get(token)
            .is_some_and(|bucket| !bucket.is_empty())
    }

    /// Check whether any *visible* notation is registered for a token.
    #[must_use]
    pub(crate) fn has_visible_notation(&self, token: &str) -> bool {
        self.entries
            .get(token)
            .is_some_and(|bucket| bucket.iter().any(|e| e.is_visible(&self.open_namespaces)))
    }

    /// Total number of registered entries across all tokens.
    #[must_use]
    pub(crate) fn entry_count(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Number of distinct tokens with registered entries.
    #[must_use]
    pub(crate) fn token_count(&self) -> usize {
        self.entries.len()
    }

    /// Iterate over all registered entries (unfiltered).
    pub(crate) fn all_entries(&self) -> impl Iterator<Item = &NotationScopeEntry> {
        self.entries.values().flat_map(|v| v.iter())
    }
}

#[cfg(test)]
#[path = "notation_scope_tests.rs"]
mod tests;
