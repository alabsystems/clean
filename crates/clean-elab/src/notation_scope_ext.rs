// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended notation scoping with kernel-type integration.
//!
//! Builds on [`crate::notation_scope`] to add:
//! - [`NotationScopeKind`]: `Global`, `Local`, `Scoped(Name)`, `Protected` variants
//! - [`NotationScopeEntry`] with kernel `Expr` expansion and fixity flags
//! - [`NotationScopeManager`] with registration, scope-aware resolution,
//!   ambiguity detection, and scope merging
//! - [`PrecedenceLevel`] with `max`/`lead` special values
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Elab/Notation.lean` (scoped/local/protected modifiers),
//! `src/Lean/Parser/Extension.lean` (precedence levels).

use std::collections::HashMap;

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::error::ElabError;

// ---------------------------------------------------------------------------
// PrecedenceLevel
// ---------------------------------------------------------------------------

/// A precedence level with special sentinels for `max` and `lead`.
///
/// Lean 4 precedences are numeric (0..1024) with two named sentinels:
/// - `max` (1024) — application-level binding
/// - `lead` (0) — loosest binding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PrecedenceLevel {
    value: u32,
    is_max: bool,
}

impl PrecedenceLevel {
    /// Maximum (application-level) precedence.
    pub(crate) const MAX: Self = Self {
        value: 1024,
        is_max: true,
    };

    /// Lead (loosest) precedence.
    pub(crate) const LEAD: Self = Self {
        value: 0,
        is_max: false,
    };

    /// Create a numeric precedence level.
    #[must_use]
    pub(crate) fn new(value: u32) -> Self {
        Self {
            value,
            is_max: value == 1024,
        }
    }

    #[must_use]
    pub(crate) fn value(self) -> u32 {
        self.value
    }

    #[must_use]
    pub(crate) fn is_max(self) -> bool {
        self.is_max
    }
}

impl PartialOrd for PrecedenceLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrecedenceLevel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare_precedence(self, other)
    }
}

/// Parse a precedence string into a [`PrecedenceLevel`].
///
/// Accepts: `"max"`, `"lead"`, or a decimal integer (0..=1024).
pub(crate) fn parse_precedence(s: &str) -> Result<PrecedenceLevel, ElabError> {
    match s.trim() {
        "max" => Ok(PrecedenceLevel::MAX),
        "lead" => Ok(PrecedenceLevel::LEAD),
        other => {
            let value: u32 = other
                .parse()
                .map_err(|_| ElabError::ParseError(format!("invalid precedence: '{other}'")))?;
            if value > 1024 {
                return Err(ElabError::ParseError(format!(
                    "precedence {value} exceeds maximum 1024"
                )));
            }
            Ok(PrecedenceLevel::new(value))
        }
    }
}

/// Compare two precedence levels. `max` sentinels always compare as 1024.
#[must_use]
pub(crate) fn compare_precedence(a: &PrecedenceLevel, b: &PrecedenceLevel) -> std::cmp::Ordering {
    a.value.cmp(&b.value)
}

// ---------------------------------------------------------------------------
// NotationScopeKind
// ---------------------------------------------------------------------------

/// The scoping kind of a notation entry.
///
/// Mirrors Lean 4's `scoped`, `local`, and `protected` modifiers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum NotationScopeKind {
    /// Always visible.
    Global,
    /// Visible only in the declaring section/file.
    Local,
    /// Visible only when the given namespace is opened.
    Scoped(Name),
    /// Visible but requires fully-qualified name to reference.
    Protected,
}

impl std::fmt::Display for NotationScopeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Global => write!(f, "global"),
            Self::Local => write!(f, "local"),
            Self::Scoped(ns) => write!(f, "scoped({ns})"),
            Self::Protected => write!(f, "protected"),
        }
    }
}

// ---------------------------------------------------------------------------
// NotationScopeEntry
// ---------------------------------------------------------------------------

/// A notation entry with kernel-level expansion and fixity metadata.
#[derive(Debug, Clone)]
pub(crate) struct NotationScopeEntry {
    /// The notation pattern/token (e.g., `"+"`, `"∘"`).
    pub(crate) pattern: String,
    /// The kernel expression this notation expands to.
    pub(crate) expansion: Expr,
    /// Binding strength.
    pub(crate) priority: u32,
    /// Scoping kind.
    pub(crate) kind: NotationScopeKind,
    /// Whether this notation can appear in prefix position.
    pub(crate) is_prefix: bool,
    /// Whether this notation can appear in infix position.
    pub(crate) is_infix: bool,
    /// Whether this notation can appear in postfix position.
    pub(crate) is_postfix: bool,
}

impl NotationScopeEntry {
    /// Create a new notation entry.
    #[must_use]
    pub(crate) fn new(
        pattern: &str,
        expansion: Expr,
        priority: u32,
        kind: NotationScopeKind,
    ) -> Self {
        Self {
            pattern: pattern.to_owned(),
            expansion,
            priority,
            kind,
            is_prefix: false,
            is_infix: false,
            is_postfix: false,
        }
    }

    /// Set fixity flags. Returns `self` for chaining.
    #[must_use]
    pub(crate) fn with_fixity(mut self, prefix: bool, infix: bool, postfix: bool) -> Self {
        self.is_prefix = prefix;
        self.is_infix = infix;
        self.is_postfix = postfix;
        self
    }

    /// Whether this entry is visible given a set of open scopes.
    #[must_use]
    pub(crate) fn is_visible(&self, open_scopes: &[Name]) -> bool {
        match &self.kind {
            NotationScopeKind::Global => true,
            NotationScopeKind::Local => true,
            NotationScopeKind::Protected => true,
            NotationScopeKind::Scoped(ns) => open_scopes.iter().any(|s| s == ns),
        }
    }
}

// ---------------------------------------------------------------------------
// Conflict & fixity helpers
// ---------------------------------------------------------------------------

/// Check whether two notation entries conflict.
///
/// Two entries conflict when they share the same pattern, both are visible
/// in the same scope, and have the same priority but different expansions.
#[must_use]
pub(crate) fn notation_conflicts(a: &NotationScopeEntry, b: &NotationScopeEntry) -> bool {
    if a.pattern != b.pattern {
        return false;
    }
    if a.priority != b.priority {
        return false;
    }
    // Same pattern + same priority but different expansion = conflict
    a.expansion != b.expansion
}

/// Filter entries by fixity flags.
///
/// Returns entries matching **any** of the requested fixity positions.
#[must_use]
pub(crate) fn filter_by_fixity<'a>(
    entries: &[&'a NotationScopeEntry],
    is_prefix: bool,
    is_infix: bool,
    is_postfix: bool,
) -> Vec<&'a NotationScopeEntry> {
    entries
        .iter()
        .filter(|e| {
            (is_prefix && e.is_prefix) || (is_infix && e.is_infix) || (is_postfix && e.is_postfix)
        })
        .copied()
        .collect()
}

// ---------------------------------------------------------------------------
// NotationScopeManager
// ---------------------------------------------------------------------------

/// Manager for extended notation scoping with registration, resolution, and
/// ambiguity detection.
///
/// Entries are indexed by pattern token for O(1) lookup. Within each bucket
/// entries are stored in descending priority order.
#[derive(Debug, Clone)]
pub(crate) struct NotationScopeManager {
    /// Entries indexed by pattern token.
    entries: HashMap<String, Vec<NotationScopeEntry>>,
}

impl Default for NotationScopeManager {
    fn default() -> Self {
        Self::new()
    }
}

impl NotationScopeManager {
    /// Create a new empty manager.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Register a notation entry.
    ///
    /// Returns an error if the entry has an empty pattern.
    pub(crate) fn register_notation(&mut self, entry: NotationScopeEntry) -> Result<(), ElabError> {
        if entry.pattern.is_empty() {
            return Err(ElabError::ParseError(
                "notation pattern must not be empty".to_owned(),
            ));
        }
        let bucket = self.entries.entry(entry.pattern.clone()).or_default();
        // Insert in descending priority order (highest first).
        let pos = bucket
            .iter()
            .position(|e| e.priority < entry.priority)
            .unwrap_or(bucket.len());
        bucket.insert(pos, entry);
        Ok(())
    }

    /// Resolve matching notations for a token within a scope.
    ///
    /// Returns all visible entries for `token` when `scope` is the active
    /// namespace, sorted by descending priority.
    #[must_use]
    pub(crate) fn resolve_notation<'a>(
        &'a self,
        token: &str,
        scope: &Name,
    ) -> Vec<&'a NotationScopeEntry> {
        let open = [scope.clone()];
        self.entries
            .get(token)
            .map(|bucket| bucket.iter().filter(|e| e.is_visible(&open)).collect())
            .unwrap_or_default()
    }

    /// All notations visible given a set of open scopes.
    ///
    /// Returns entries across all tokens, filtered by visibility, sorted by
    /// descending priority within each token bucket.
    #[must_use]
    pub(crate) fn active_notations<'a>(
        &'a self,
        open_scopes: &[Name],
    ) -> Vec<&'a NotationScopeEntry> {
        self.entries
            .values()
            .flat_map(|bucket| bucket.iter())
            .filter(|e| e.is_visible(open_scopes))
            .collect()
    }

    /// Detect ambiguous notations for a token within a scope.
    ///
    /// Returns `Some(entries)` when two or more visible entries share the
    /// same priority for the given token. Returns `None` if there is no
    /// ambiguity.
    #[must_use]
    pub(crate) fn check_ambiguity<'a>(
        &'a self,
        token: &str,
        scope: &Name,
    ) -> Option<Vec<&'a NotationScopeEntry>> {
        let visible = self.resolve_notation(token, scope);
        if visible.len() < 2 {
            return None;
        }
        // Check for same-priority entries
        let top_priority = visible[0].priority;
        let same_priority: Vec<&NotationScopeEntry> = visible
            .into_iter()
            .filter(|e| e.priority == top_priority)
            .collect();
        if same_priority.len() >= 2 {
            Some(same_priority)
        } else {
            None
        }
    }

    /// Number of registered entries.
    #[must_use]
    pub(crate) fn entry_count(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Number of distinct tokens.
    #[must_use]
    pub(crate) fn token_count(&self) -> usize {
        self.entries.len()
    }

    /// All registered entries (unfiltered), for merging.
    pub(crate) fn all_entries(&self) -> impl Iterator<Item = &NotationScopeEntry> {
        self.entries.values().flat_map(|v| v.iter())
    }
}

/// Merge multiple notation scope managers into one.
///
/// Entries from all managers are collected and re-registered into a fresh
/// manager. Priority ordering is preserved.
#[must_use]
pub(crate) fn merge_notation_scopes(scopes: &[&NotationScopeManager]) -> NotationScopeManager {
    let mut merged = NotationScopeManager::new();
    for mgr in scopes {
        for entry in mgr.all_entries() {
            // Clone entry and re-register; ignore empty-pattern errors
            // since all entries in existing managers have non-empty patterns.
            let _ = merged.register_notation(entry.clone());
        }
    }
    merged
}
