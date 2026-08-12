#![allow(dead_code)]
// 2026-08-04: staged notation prototype, cfg(test)-gated; module-level allow
// avoids ~26 per-item annotations pushing this file past the 500-line rule.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended notation elaboration for Lean 5.
//!
//! Provides mixfix notation parsing, precedence management, macro expansion,
//! scoped notation, overloading, dynamic registration, pretty-print integration,
//! conflict detection, and deprecation support.
//!
//! Builds on [`crate::notation`] (registry) and [`crate::notation_priority`]
//! (precedence resolver) to deliver the full notation pipeline needed for
//! Lean 4 elaboration parity.
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Elab/Notation.lean`, `src/Lean/PrettyPrinter/Delaborator/Builtins.lean`.

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
use std::collections::{HashMap, HashSet};

use clean_kernel::{Expr, Name};

use crate::notation_priority::{Associativity, MixfixItem, MixfixPattern, NotationPriority};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// The kind of a notation entry, describing its syntactic position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum NotationKindExt {
    Prefix,
    Postfix,
    InfixLeft,
    InfixRight,
    InfixNone,
    Mixfix,
}

impl NotationKindExt {
    #[must_use]
    pub(crate) fn associativity(self) -> Associativity {
        match self {
            Self::InfixLeft => Associativity::Left,
            Self::InfixRight => Associativity::Right,
            Self::InfixNone | Self::Prefix | Self::Postfix | Self::Mixfix => Associativity::None,
        }
    }

    #[must_use]
    pub(crate) fn is_infix(self) -> bool {
        matches!(self, Self::InfixLeft | Self::InfixRight | Self::InfixNone)
    }
}

/// Configuration for the extended notation system.
#[derive(Debug, Clone)]
pub(crate) struct NotationExtConfig {
    /// Maximum depth when expanding notation macros (prevents infinite loops).
    pub(crate) max_expansion_depth: u32,
    /// Whether to warn on deprecated notation usage.
    pub(crate) warn_deprecated: bool,
    /// Whether to detect and report notation conflicts.
    pub(crate) detect_conflicts: bool,
}

impl Default for NotationExtConfig {
    fn default() -> Self {
        Self {
            max_expansion_depth: 64,
            warn_deprecated: true,
            detect_conflicts: true,
        }
    }
}

/// A registered extended notation entry.
#[derive(Debug, Clone)]
pub(crate) struct ExtNotationEntry {
    pub(crate) name: Name,
    pub(crate) pattern: MixfixPattern,
    pub(crate) expansion: Expr,
    pub(crate) priority: NotationPriority,
    pub(crate) kind: NotationKindExt,
    pub(crate) scope: Option<Name>,
    pub(crate) deprecated: bool,
    pub(crate) deprecation_msg: Option<String>,
    active: bool,
}

impl ExtNotationEntry {
    #[must_use]
    pub(crate) fn new(
        name: Name,
        pattern: MixfixPattern,
        expansion: Expr,
        priority: NotationPriority,
        kind: NotationKindExt,
    ) -> Self {
        Self {
            name,
            pattern,
            expansion,
            priority,
            kind,
            scope: None,
            deprecated: false,
            deprecation_msg: None,
            active: true,
        }
    }

    #[must_use]
    pub(crate) fn with_scope(mut self, ns: Name) -> Self {
        self.scope = Some(ns);
        self
    }

    #[must_use]
    pub(crate) fn with_deprecation(mut self, msg: &str) -> Self {
        self.deprecated = true;
        self.deprecation_msg = Some(msg.to_owned());
        self
    }

    #[must_use]
    pub(crate) fn is_active(&self) -> bool {
        self.active
    }

    pub(crate) fn deactivate(&mut self) {
        self.active = false;
    }

    pub(crate) fn reactivate(&mut self) {
        self.active = true;
    }
}

// ---------------------------------------------------------------------------
// Conflict detection
// ---------------------------------------------------------------------------

/// A conflict between two notation entries that share overlapping syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NotationConflict {
    pub(crate) token: String,
    pub(crate) first: Name,
    pub(crate) second: Name,
    pub(crate) reason: ConflictReason,
}

/// Why two notations conflict.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ConflictReason {
    /// Same leading token at the same precedence with different associativity.
    AssociativityMismatch,
    /// Identical pattern shape with different expansions.
    OverlappingPattern,
}

impl std::fmt::Display for NotationConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "notation conflict for '{}': {} vs {} ({:?})",
            self.token, self.first, self.second, self.reason,
        )
    }
}

// ---------------------------------------------------------------------------
// Deprecation warning
// ---------------------------------------------------------------------------

/// A warning produced when using a deprecated notation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeprecationWarning {
    pub(crate) notation_name: Name,
    pub(crate) message: String,
}

// ---------------------------------------------------------------------------
// Pretty-print fragment
// ---------------------------------------------------------------------------

/// A fragment of a pretty-print format generated from a notation definition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum PrettyFragment {
    /// Literal text token.
    Lit(String),
    /// Placeholder for the n-th argument.
    Arg(usize),
    /// Whitespace separator.
    Space,
}

/// Generate pretty-print fragments from a mixfix pattern.
#[must_use]
pub(crate) fn pretty_fragments_from_pattern(pattern: &MixfixPattern) -> Vec<PrettyFragment> {
    let mut frags = Vec::new();
    for (i, item) in pattern.items().iter().enumerate() {
        if i > 0 {
            frags.push(PrettyFragment::Space);
        }
        match item {
            MixfixItem::Token(t) => frags.push(PrettyFragment::Lit(t.clone())),
            MixfixItem::Arg(n) => frags.push(PrettyFragment::Arg(*n)),
        }
    }
    frags
}

/// Render pretty-print fragments into a format string (e.g., `"_ + _"`).
#[must_use]
pub(crate) fn render_pretty_fragments(frags: &[PrettyFragment]) -> String {
    let mut out = String::new();
    for frag in frags {
        match frag {
            PrettyFragment::Lit(s) => out.push_str(s),
            PrettyFragment::Arg(_) => out.push('_'),
            PrettyFragment::Space => out.push(' '),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Expansion
// ---------------------------------------------------------------------------

/// Result of expanding a notation.
#[derive(Debug, Clone)]
pub(crate) struct ExpansionResult {
    pub(crate) expr: Expr,
    pub(crate) warnings: Vec<DeprecationWarning>,
}

/// Expand a notation entry with the given arguments.
///
/// Substitutes each `Arg(i)` placeholder in the pattern's expansion with
/// `args[i]`. Returns `None` if arity mismatch.
#[must_use]
pub(crate) fn expand_notation(
    entry: &ExtNotationEntry,
    args: &[Expr],
    config: &NotationExtConfig,
) -> Option<ExpansionResult> {
    if args.len() != entry.pattern.arity() {
        return None;
    }
    let mut warnings = Vec::new();
    if config.warn_deprecated && entry.deprecated {
        warnings.push(DeprecationWarning {
            notation_name: entry.name.clone(),
            message: entry
                .deprecation_msg
                .clone()
                .unwrap_or_else(|| format!("notation '{}' is deprecated", entry.name)),
        });
    }
    // Build application: entry.expansion applied to args left-to-right.
    let expr = Expr::apps_ref(entry.expansion.clone(), args);
    Some(ExpansionResult { expr, warnings })
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

/// Extended notation registry with scoping, overloading, conflict detection,
/// and deprecation tracking.
#[derive(Debug)]
pub(crate) struct ExtNotationRegistry {
    entries: Vec<ExtNotationEntry>,
    /// Token -> entry indices (for lookup by leading token).
    token_index: HashMap<String, Vec<usize>>,
    /// Currently open namespaces (scoped notations are visible only when their
    /// namespace is in this set).
    open_namespaces: HashSet<Name>,
    config: NotationExtConfig,
}

impl Default for ExtNotationRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl ExtNotationRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::with_config(NotationExtConfig::default())
    }

    #[must_use]
    pub(crate) fn with_config(config: NotationExtConfig) -> Self {
        Self {
            entries: Vec::new(),
            token_index: HashMap::new(),
            open_namespaces: HashSet::new(),
            config,
        }
    }

    /// Register a new notation entry. Returns the entry index.
    pub(crate) fn register(&mut self, entry: ExtNotationEntry) -> usize {
        let idx = self.entries.len();
        let key = entry.pattern.leading_token().unwrap_or("").to_owned();
        self.token_index.entry(key).or_default().push(idx);
        self.entries.push(entry);
        idx
    }

    /// Open a namespace, making its scoped notations visible.
    pub(crate) fn open_namespace(&mut self, ns: Name) {
        self.open_namespaces.insert(ns);
    }

    /// Close a namespace, hiding its scoped notations.
    pub(crate) fn close_namespace(&mut self, ns: &Name) {
        self.open_namespaces.remove(ns);
    }

    /// Check whether a scoped entry is visible under current namespace state.
    fn is_visible(&self, entry: &ExtNotationEntry) -> bool {
        if !entry.is_active() {
            return false;
        }
        match &entry.scope {
            None => true, // global
            Some(ns) => self.open_namespaces.contains(ns),
        }
    }

    /// Resolve the highest-priority visible notation for a token.
    #[must_use]
    pub(crate) fn resolve(&self, token: &str) -> Option<&ExtNotationEntry> {
        self.token_index
            .get(token)?
            .iter()
            .filter_map(|&idx| {
                let e = &self.entries[idx];
                if self.is_visible(e) {
                    Some(e)
                } else {
                    None
                }
            })
            .max_by_key(|e| e.priority)
    }

    /// All visible entries for a token, descending by priority (for overloading).
    #[must_use]
    pub(crate) fn resolve_all(&self, token: &str) -> Vec<&ExtNotationEntry> {
        let Some(indices) = self.token_index.get(token) else {
            return Vec::new();
        };
        let mut result: Vec<&ExtNotationEntry> = indices
            .iter()
            .filter_map(|&idx| {
                let e = &self.entries[idx];
                if self.is_visible(e) {
                    Some(e)
                } else {
                    None
                }
            })
            .collect();
        result.sort_by_key(|b| std::cmp::Reverse(b.priority));
        result
    }

    /// Detect notation conflicts among visible entries.
    #[must_use]
    pub(crate) fn detect_conflicts(&self) -> Vec<NotationConflict> {
        if !self.config.detect_conflicts {
            return Vec::new();
        }
        let mut conflicts = Vec::new();
        for (token, indices) in &self.token_index {
            let visible: Vec<&ExtNotationEntry> = indices
                .iter()
                .filter_map(|&idx| {
                    let e = &self.entries[idx];
                    if self.is_visible(e) {
                        Some(e)
                    } else {
                        None
                    }
                })
                .collect();
            for i in 0..visible.len() {
                for j in (i + 1)..visible.len() {
                    let a = visible[i];
                    let b = visible[j];
                    // Associativity mismatch at same precedence
                    if a.priority == b.priority && a.kind.associativity() != b.kind.associativity()
                    {
                        conflicts.push(NotationConflict {
                            token: token.clone(),
                            first: a.name.clone(),
                            second: b.name.clone(),
                            reason: ConflictReason::AssociativityMismatch,
                        });
                    }
                    // Overlapping pattern (same tokens in same order)
                    if a.pattern.items() == b.pattern.items() && a.name != b.name {
                        conflicts.push(NotationConflict {
                            token: token.clone(),
                            first: a.name.clone(),
                            second: b.name.clone(),
                            reason: ConflictReason::OverlappingPattern,
                        });
                    }
                }
            }
        }
        conflicts
    }

    /// Expand the highest-priority visible notation for a token with the given args.
    #[must_use]
    pub(crate) fn expand(&self, token: &str, args: &[Expr]) -> Option<ExpansionResult> {
        let entry = self.resolve(token)?;
        expand_notation(entry, args, &self.config)
    }

    /// Generate pretty-print fragments for a token's highest-priority notation.
    #[must_use]
    pub(crate) fn pretty_print(&self, token: &str) -> Option<Vec<PrettyFragment>> {
        let entry = self.resolve(token)?;
        Some(pretty_fragments_from_pattern(&entry.pattern))
    }

    pub(crate) fn deactivate(&mut self, idx: usize) {
        if idx < self.entries.len() {
            self.entries[idx].deactivate();
        }
    }

    pub(crate) fn reactivate(&mut self, idx: usize) {
        if idx < self.entries.len() {
            self.entries[idx].reactivate();
        }
    }

    #[must_use]
    pub(crate) fn entry_count(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn visible_count(&self) -> usize {
        self.entries.iter().filter(|e| self.is_visible(e)).count()
    }

    #[must_use]
    pub(crate) fn config(&self) -> &NotationExtConfig {
        &self.config
    }

    /// Deprecate a notation by index.
    pub(crate) fn deprecate(&mut self, idx: usize, msg: &str) {
        if idx < self.entries.len() {
            self.entries[idx].deprecated = true;
            self.entries[idx].deprecation_msg = Some(msg.to_owned());
        }
    }

    /// Access an entry by index.
    #[must_use]
    pub(crate) fn get(&self, idx: usize) -> Option<&ExtNotationEntry> {
        self.entries.get(idx)
    }

    /// Check whether any visible notation exists for a token.
    #[must_use]
    pub(crate) fn has_notation(&self, token: &str) -> bool {
        self.resolve(token).is_some()
    }
}
