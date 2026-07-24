// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Notation priority, associativity, and mixfix elaboration for Lean 5.
//!
//! Resolves operator binding strength and associativity to produce
//! correctly-parenthesized application trees during elaboration.
//!
//! Core types: [`Associativity`], [`NotationPriority`], [`MixfixPattern`],
//! [`PriorityEntry`], [`PriorityScopeStack`], [`PriorityResolver`].
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Parser/Extension.lean` (priorities), `src/Lean/Elab/Notation.lean`
//! (mixfix). Priorities 0..1024, higher binds tighter. Associativity encoded
//! in notation kind (`infixl`, `infixr`).

use std::collections::HashMap;

/// Operator associativity for infix notations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Associativity {
    /// `a op b op c` = `(a op b) op c`.
    Left,
    /// `a op b op c` = `a op (b op c)`.
    Right,
    /// Chaining is an error; requires explicit parentheses.
    None,
}

impl std::fmt::Display for Associativity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Left => write!(f, "left"),
            Self::Right => write!(f, "right"),
            Self::None => write!(f, "none"),
        }
    }
}

/// Typed wrapper for notation priority (precedence). Higher = tighter binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NotationPriority(u32);

impl NotationPriority {
    pub(crate) const MAX: Self = Self(1024);
    pub(crate) const LEAD: Self = Self(0);
    pub(crate) const DEFAULT: Self = Self(0);
    pub(crate) const ADD: Self = Self(65);
    pub(crate) const MUL: Self = Self(70);
    pub(crate) const APP: Self = Self(1024);

    #[must_use]
    pub(crate) const fn new(value: u32) -> Self {
        Self(value)
    }

    #[must_use]
    pub(crate) const fn value(self) -> u32 {
        self.0
    }

    #[must_use]
    pub(crate) const fn is_tighter_than(self, other: Self) -> bool {
        self.0 > other.0
    }
}

impl std::fmt::Display for NotationPriority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An item in a mixfix notation pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum MixfixItem {
    /// A literal keyword token.
    Token(String),
    /// An argument placeholder with positional index.
    Arg(usize),
}

/// A mixfix notation pattern: sequence of tokens and argument slots.
///
/// Captures infix, prefix, postfix, and general mixfix shapes like
/// `if _ then _ else _` or `⟨_, _, _⟩`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MixfixPattern {
    items: Vec<MixfixItem>,
}

impl MixfixPattern {
    #[must_use]
    pub(crate) fn new(items: Vec<MixfixItem>) -> Self {
        Self { items }
    }

    /// `token _`
    #[must_use]
    pub(crate) fn prefix(token: &str) -> Self {
        Self {
            items: vec![MixfixItem::Token(token.to_owned()), MixfixItem::Arg(0)],
        }
    }

    /// `_ token _`
    #[must_use]
    pub(crate) fn infix(token: &str) -> Self {
        Self {
            items: vec![
                MixfixItem::Arg(0),
                MixfixItem::Token(token.to_owned()),
                MixfixItem::Arg(1),
            ],
        }
    }

    /// `_ token`
    #[must_use]
    pub(crate) fn postfix(token: &str) -> Self {
        Self {
            items: vec![MixfixItem::Arg(0), MixfixItem::Token(token.to_owned())],
        }
    }

    /// Number of argument placeholders.
    #[must_use]
    pub(crate) fn arity(&self) -> usize {
        self.items
            .iter()
            .filter(|i| matches!(i, MixfixItem::Arg(_)))
            .count()
    }

    /// Leading token (first `Token`), skipping any leading `Arg`. For indexing.
    #[must_use]
    pub(crate) fn leading_token(&self) -> Option<&str> {
        self.items.iter().find_map(|i| match i {
            MixfixItem::Token(t) => Some(t.as_str()),
            MixfixItem::Arg(_) => None,
        })
    }

    /// All literal tokens in order.
    #[must_use]
    pub(crate) fn tokens(&self) -> Vec<&str> {
        self.items
            .iter()
            .filter_map(|i| match i {
                MixfixItem::Token(t) => Some(t.as_str()),
                MixfixItem::Arg(_) => None,
            })
            .collect()
    }

    /// Whether pattern starts with an argument (led position, e.g. infix).
    #[must_use]
    pub(crate) fn is_led(&self) -> bool {
        matches!(self.items.first(), Some(MixfixItem::Arg(_)))
    }

    #[must_use]
    pub(crate) fn items(&self) -> &[MixfixItem] {
        &self.items
    }
}

/// A notation with full priority and associativity metadata.
#[derive(Debug, Clone)]
pub(crate) struct PriorityEntry {
    name: String,
    pattern: MixfixPattern,
    priority: NotationPriority,
    assoc: Associativity,
    namespace: Option<String>,
    is_local: bool,
    is_deactivated: bool,
}

impl PriorityEntry {
    #[must_use]
    pub(crate) fn new(
        name: &str,
        pattern: MixfixPattern,
        priority: NotationPriority,
        assoc: Associativity,
    ) -> Self {
        Self {
            name: name.to_owned(),
            pattern,
            priority,
            assoc,
            namespace: None,
            is_local: false,
            is_deactivated: false,
        }
    }

    #[must_use]
    pub(crate) fn with_namespace(mut self, ns: &str) -> Self {
        self.namespace = Some(ns.to_owned());
        self
    }

    #[must_use]
    pub(crate) fn with_local(mut self) -> Self {
        self.is_local = true;
        self
    }

    #[must_use]
    pub(crate) fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub(crate) fn pattern(&self) -> &MixfixPattern {
        &self.pattern
    }
    #[must_use]
    pub(crate) fn priority(&self) -> NotationPriority {
        self.priority
    }
    #[must_use]
    pub(crate) fn assoc(&self) -> Associativity {
        self.assoc
    }
    #[must_use]
    pub(crate) fn is_active(&self) -> bool {
        !self.is_deactivated
    }

    pub(crate) fn deactivate(&mut self) {
        self.is_deactivated = true;
    }
    pub(crate) fn reactivate(&mut self) {
        self.is_deactivated = false;
    }
}

/// A conflict between two entries at the same precedence with different assoc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PriorityConflict {
    pub(crate) token: String,
    pub(crate) priority: NotationPriority,
    pub(crate) first: String,
    pub(crate) second: String,
}

impl std::fmt::Display for PriorityConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "notation conflict at priority {} for '{}': '{}' vs '{}'",
            self.priority, self.token, self.first, self.second,
        )
    }
}

/// A scope frame tracking entries registered in a given scope level.
#[derive(Debug, Clone)]
struct ScopeFrame {
    entry_indices: Vec<usize>,
    inherited_priority: Option<NotationPriority>,
}

/// Stack of nested notation scopes with priority inheritance.
///
/// Push on section/namespace entry, pop on exit. Entries registered in a
/// scope are deactivated when that scope is popped. Child scopes can
/// inherit the priority of their parent.
#[derive(Debug)]
pub(crate) struct PriorityScopeStack {
    frames: Vec<ScopeFrame>,
    root_priority: NotationPriority,
}

impl Default for PriorityScopeStack {
    fn default() -> Self {
        Self::new()
    }
}

impl PriorityScopeStack {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            frames: Vec::new(),
            root_priority: NotationPriority::DEFAULT,
        }
    }

    pub(crate) fn push_scope(&mut self, inherit_priority: bool) {
        let inherited = if inherit_priority {
            Some(self.current_priority())
        } else {
            None
        };
        self.frames.push(ScopeFrame {
            entry_indices: Vec::new(),
            inherited_priority: inherited,
        });
    }

    /// Pop scope, returning entry indices registered in it (for deactivation).
    pub(crate) fn pop_scope(&mut self) -> Option<Vec<usize>> {
        self.frames.pop().map(|f| f.entry_indices)
    }

    pub(crate) fn track_entry(&mut self, idx: usize) {
        if let Some(frame) = self.frames.last_mut() {
            frame.entry_indices.push(idx);
        }
    }

    /// Inherited priority from innermost scope, or root priority.
    #[must_use]
    pub(crate) fn current_priority(&self) -> NotationPriority {
        self.frames
            .iter()
            .rev()
            .find_map(|f| f.inherited_priority)
            .unwrap_or(self.root_priority)
    }

    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.frames.len()
    }
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    pub(crate) fn set_root_priority(&mut self, priority: NotationPriority) {
        self.root_priority = priority;
    }
}

/// Priority-aware notation resolver with conflict detection and scoping.
///
/// Resolution rules:
/// 1. Only active (non-deactivated) entries are considered.
/// 2. Highest priority wins.
/// 3. At equal priority, most recently registered wins.
/// 4. Associativity conflicts (same token+priority, different assoc) are
///    detected but not rejected -- the caller decides.
#[derive(Debug)]
pub(crate) struct PriorityResolver {
    entries: Vec<PriorityEntry>,
    token_index: HashMap<String, Vec<usize>>,
    scopes: PriorityScopeStack,
}

impl Default for PriorityResolver {
    fn default() -> Self {
        Self::new()
    }
}

impl PriorityResolver {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            token_index: HashMap::new(),
            scopes: PriorityScopeStack::new(),
        }
    }

    /// Register an entry, returning its index.
    pub(crate) fn register(&mut self, entry: PriorityEntry) -> usize {
        let idx = self.entries.len();
        let key = entry.pattern.leading_token().unwrap_or("").to_owned();
        self.token_index.entry(key).or_default().push(idx);
        self.scopes.track_entry(idx);
        self.entries.push(entry);
        idx
    }

    /// Resolve highest-priority active entry for a token.
    #[must_use]
    pub(crate) fn resolve(&self, token: &str) -> Option<&PriorityEntry> {
        self.token_index
            .get(token)?
            .iter()
            .filter_map(|&idx| {
                let e = &self.entries[idx];
                if e.is_active() {
                    Some(e)
                } else {
                    None
                }
            })
            .max_by_key(|e| e.priority)
    }

    /// All active entries for a token, descending priority.
    #[must_use]
    pub(crate) fn resolve_all(&self, token: &str) -> Vec<&PriorityEntry> {
        let Some(indices) = self.token_index.get(token) else {
            return Vec::new();
        };
        let mut result: Vec<&PriorityEntry> = indices
            .iter()
            .filter_map(|&idx| {
                let e = &self.entries[idx];
                if e.is_active() {
                    Some(e)
                } else {
                    None
                }
            })
            .collect();
        result.sort_by_key(|b| std::cmp::Reverse(b.priority));
        result
    }

    /// Detect associativity conflicts: same token+priority, different assoc.
    #[must_use]
    pub(crate) fn detect_conflicts(&self) -> Vec<PriorityConflict> {
        let mut conflicts = Vec::new();
        for (token, indices) in &self.token_index {
            let active: Vec<&PriorityEntry> = indices
                .iter()
                .filter_map(|&idx| {
                    let e = &self.entries[idx];
                    if e.is_active() {
                        Some(e)
                    } else {
                        None
                    }
                })
                .collect();
            for i in 0..active.len() {
                for j in (i + 1)..active.len() {
                    if active[i].priority == active[j].priority
                        && active[i].assoc != active[j].assoc
                    {
                        conflicts.push(PriorityConflict {
                            token: token.clone(),
                            priority: active[i].priority,
                            first: active[i].name.clone(),
                            second: active[j].name.clone(),
                        });
                    }
                }
            }
        }
        conflicts
    }

    pub(crate) fn push_scope(&mut self, inherit_priority: bool) {
        self.scopes.push_scope(inherit_priority);
    }

    /// Pop scope, deactivating all entries registered in it.
    pub(crate) fn pop_scope(&mut self) {
        if let Some(indices) = self.scopes.pop_scope() {
            for idx in indices {
                if idx < self.entries.len() {
                    self.entries[idx].deactivate();
                }
            }
        }
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
    pub(crate) fn current_scope_priority(&self) -> NotationPriority {
        self.scopes.current_priority()
    }

    #[must_use]
    pub(crate) fn scope_depth(&self) -> usize {
        self.scopes.depth()
    }
    #[must_use]
    pub(crate) fn entry_count(&self) -> usize {
        self.entries.len()
    }
    #[must_use]
    pub(crate) fn active_count(&self) -> usize {
        self.entries.iter().filter(|e| e.is_active()).count()
    }
    #[must_use]
    pub(crate) fn has_active_notation(&self, token: &str) -> bool {
        self.resolve(token).is_some()
    }
}
