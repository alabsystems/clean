// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended notation scope handling with scope stacking, inheritance,
//! conflict detection, and export/import.
//!
//! Builds on [`crate::notation_scope`] and [`crate::notation_scope_ext`].
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Elab/Notation.lean`, `src/Lean/ScopedEnvExtension.lean`.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use clean_kernel::name::Name;

/// Errors specific to extended notation scope operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum NotationScopeError {
    #[error("scope not found: {0}")]
    ScopeNotFound(Name),
    #[error(
        "notation conflict in scope {scope}: '{syntax}' defined by both '{first}' and '{second}'"
    )]
    Conflict {
        scope: Name,
        syntax: String,
        first: Name,
        second: Name,
    },
    #[error("export target scope not found: {0}")]
    ExportTargetNotFound(Name),
    #[error("import source scope not found: {0}")]
    ImportSourceNotFound(Name),
    #[error("scope already exists: {0}")]
    DuplicateScope(Name),
}

/// A notation entry within a named scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopedNotation {
    pub(crate) qualified_name: Name,
    pub(crate) syntax: String,
    pub(crate) expansion: String,
    pub(crate) priority: u32,
}

impl ScopedNotation {
    #[must_use]
    pub(crate) fn new(qualified_name: Name, syntax: &str, expansion: &str, priority: u32) -> Self {
        Self {
            qualified_name,
            syntax: syntax.to_owned(),
            expansion: expansion.to_owned(),
            priority,
        }
    }
}

/// An abbreviation visible only within its declaring scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopedAbbreviation {
    pub(crate) short_name: String,
    pub(crate) expansion: String,
    pub(crate) scope: Name,
}

impl ScopedAbbreviation {
    #[must_use]
    pub(crate) fn new(short_name: &str, expansion: &str, scope: Name) -> Self {
        Self {
            short_name: short_name.to_owned(),
            expansion: expansion.to_owned(),
            scope,
        }
    }
}

/// A single named notation scope with optional parent for inheritance.
#[derive(Debug, Clone)]
pub(crate) struct NotationScope {
    name: Name,
    parent: Option<Name>,
    notations: HashMap<String, ScopedNotation>,
    abbreviations: HashMap<String, ScopedAbbreviation>,
}

impl NotationScope {
    #[must_use]
    pub(crate) fn new(name: Name, parent: Option<Name>) -> Self {
        Self {
            name,
            parent,
            notations: HashMap::new(),
            abbreviations: HashMap::new(),
        }
    }

    #[must_use]
    pub(crate) fn name(&self) -> &Name {
        &self.name
    }

    #[must_use]
    pub(crate) fn parent(&self) -> Option<&Name> {
        self.parent.as_ref()
    }

    pub(crate) fn add_notation(&mut self, n: ScopedNotation) {
        self.notations.insert(n.syntax.clone(), n);
    }

    pub(crate) fn add_abbreviation(&mut self, a: ScopedAbbreviation) {
        self.abbreviations.insert(a.short_name.clone(), a);
    }

    #[must_use]
    pub(crate) fn get_notation(&self, syntax: &str) -> Option<&ScopedNotation> {
        self.notations.get(syntax)
    }

    #[must_use]
    pub(crate) fn get_abbreviation(&self, short_name: &str) -> Option<&ScopedAbbreviation> {
        self.abbreviations.get(short_name)
    }

    pub(crate) fn notations(&self) -> impl Iterator<Item = &ScopedNotation> {
        self.notations.values()
    }

    #[must_use]
    pub(crate) fn notation_count(&self) -> usize {
        self.notations.len()
    }

    #[must_use]
    pub(crate) fn abbreviation_count(&self) -> usize {
        self.abbreviations.len()
    }
}

/// Statistics about the scope registry.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ScopeStats {
    pub(crate) scopes_defined: usize,
    pub(crate) scopes_active: usize,
    pub(crate) lookups: u64,
    pub(crate) conflicts: u64,
    pub(crate) exports: u64,
}

/// Extended notation scope registry with stacking, inheritance, and
/// conflict detection.
///
/// Active scopes form a stack; inner (later-opened) scopes shadow outer.
/// A scope may declare a parent; the parent chain is consulted when a
/// notation is not found directly.
pub(crate) struct NotationScopeRegistry2 {
    scopes: HashMap<Name, NotationScope>,
    active_stack: Vec<Name>,
    default_scopes: Vec<Name>,
    stat_lookups: Cell<u64>,
    stat_conflicts: Cell<u64>,
    stat_exports: Cell<u64>,
}

impl std::fmt::Debug for NotationScopeRegistry2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NotationScopeRegistry2")
            .field("scope_count", &self.scopes.len())
            .field("active_count", &self.active_stack.len())
            .field("lookups", &self.stat_lookups.get())
            .finish()
    }
}

impl Default for NotationScopeRegistry2 {
    fn default() -> Self {
        Self::new()
    }
}

impl NotationScopeRegistry2 {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            scopes: HashMap::new(),
            active_stack: Vec::new(),
            default_scopes: Vec::new(),
            stat_lookups: Cell::new(0),
            stat_conflicts: Cell::new(0),
            stat_exports: Cell::new(0),
        }
    }

    /// Define a new scope with an optional parent for inheritance.
    pub(crate) fn define_scope(
        &mut self,
        name: Name,
        parent: Option<Name>,
    ) -> Result<(), NotationScopeError> {
        if self.scopes.contains_key(&name) {
            return Err(NotationScopeError::DuplicateScope(name));
        }
        self.scopes
            .insert(name.clone(), NotationScope::new(name, parent));
        Ok(())
    }

    #[must_use]
    pub(crate) fn is_scope_defined(&self, name: &Name) -> bool {
        self.scopes.contains_key(name)
    }

    /// Activate (open) a scope, pushing it onto the active stack.
    /// If already active, it is moved to the top.
    pub(crate) fn activate_scope(&mut self, name: &Name) -> Result<(), NotationScopeError> {
        if !self.scopes.contains_key(name) {
            return Err(NotationScopeError::ScopeNotFound(name.clone()));
        }
        self.active_stack.retain(|n| n != name);
        self.active_stack.push(name.clone());
        Ok(())
    }

    /// Deactivate (close) a scope, removing it from the active stack.
    pub(crate) fn deactivate_scope(&mut self, name: &Name) -> Result<(), NotationScopeError> {
        if !self.scopes.contains_key(name) {
            return Err(NotationScopeError::ScopeNotFound(name.clone()));
        }
        self.active_stack.retain(|n| n != name);
        Ok(())
    }

    #[must_use]
    pub(crate) fn is_scope_active(&self, name: &Name) -> bool {
        self.active_stack.iter().any(|n| n == name)
    }

    #[must_use]
    pub(crate) fn active_scopes(&self) -> &[Name] {
        &self.active_stack
    }

    pub(crate) fn set_default_scopes(&mut self, defaults: Vec<Name>) {
        self.default_scopes = defaults;
    }

    /// Activate all default scopes. Undefined scopes are silently skipped.
    pub(crate) fn activate_defaults(&mut self) {
        let defaults: Vec<Name> = self.default_scopes.clone();
        for name in &defaults {
            if self.scopes.contains_key(name) {
                let _ = self.activate_scope(name);
            }
        }
    }

    #[must_use]
    pub(crate) fn default_scopes(&self) -> &[Name] {
        &self.default_scopes
    }

    /// Register a notation in a scope.
    pub(crate) fn register_notation(
        &mut self,
        scope_name: &Name,
        notation: ScopedNotation,
    ) -> Result<(), NotationScopeError> {
        self.scopes
            .get_mut(scope_name)
            .ok_or_else(|| NotationScopeError::ScopeNotFound(scope_name.clone()))?
            .add_notation(notation);
        Ok(())
    }

    /// Register an abbreviation in a scope.
    pub(crate) fn register_abbreviation(
        &mut self,
        scope_name: &Name,
        abbr: ScopedAbbreviation,
    ) -> Result<(), NotationScopeError> {
        self.scopes
            .get_mut(scope_name)
            .ok_or_else(|| NotationScopeError::ScopeNotFound(scope_name.clone()))?
            .add_abbreviation(abbr);
        Ok(())
    }

    /// Look up a notation by syntax, searching the active scope stack
    /// from top to bottom. For each scope, walks the parent chain.
    #[must_use]
    pub(crate) fn lookup_notation(&self, syntax: &str) -> Option<&ScopedNotation> {
        self.stat_lookups.set(self.stat_lookups.get() + 1);
        for scope_name in self.active_stack.iter().rev() {
            if let Some(n) = self.lookup_in_scope_chain(scope_name, syntax) {
                return Some(n);
            }
        }
        None
    }

    /// Look up all matching notations across active scopes, sorted by
    /// descending priority.
    #[must_use]
    pub(crate) fn lookup_all_notations(&self, syntax: &str) -> Vec<&ScopedNotation> {
        self.stat_lookups.set(self.stat_lookups.get() + 1);
        let mut results = Vec::new();
        let mut seen = HashSet::new();
        for scope_name in self.active_stack.iter().rev() {
            self.collect_from_chain(scope_name, syntax, &mut results, &mut seen);
        }
        results.sort_by_key(|b| std::cmp::Reverse(b.priority));
        results
    }

    /// Look up an abbreviation by short name across active scopes.
    #[must_use]
    pub(crate) fn lookup_abbreviation(&self, short_name: &str) -> Option<&ScopedAbbreviation> {
        for scope_name in self.active_stack.iter().rev() {
            if let Some(scope) = self.scopes.get(scope_name) {
                if let Some(abbr) = scope.get_abbreviation(short_name) {
                    return Some(abbr);
                }
            }
        }
        None
    }

    fn lookup_in_scope_chain(&self, scope_name: &Name, syntax: &str) -> Option<&ScopedNotation> {
        let mut current = Some(scope_name);
        let mut visited = HashSet::new();
        while let Some(name) = current {
            if !visited.insert(name.clone()) {
                break;
            }
            if let Some(scope) = self.scopes.get(name) {
                if let Some(n) = scope.get_notation(syntax) {
                    return Some(n);
                }
                current = scope.parent.as_ref();
            } else {
                break;
            }
        }
        None
    }

    fn collect_from_chain<'a>(
        &'a self,
        scope_name: &Name,
        syntax: &str,
        results: &mut Vec<&'a ScopedNotation>,
        seen: &mut HashSet<Name>,
    ) {
        let mut current = Some(scope_name);
        while let Some(name) = current {
            if !seen.insert(name.clone()) {
                break;
            }
            if let Some(scope) = self.scopes.get(name) {
                if let Some(n) = scope.get_notation(syntax) {
                    results.push(n);
                }
                current = scope.parent.as_ref();
            } else {
                break;
            }
        }
    }

    /// Detect cross-scope conflicts among all active scopes.
    #[must_use]
    pub(crate) fn detect_active_conflicts(&self) -> Vec<NotationScopeError> {
        let mut errors = Vec::new();
        let mut by_syntax: HashMap<(&str, u32), Vec<(&Name, &ScopedNotation)>> = HashMap::new();
        for scope_name in &self.active_stack {
            if let Some(scope) = self.scopes.get(scope_name) {
                for notation in scope.notations() {
                    by_syntax
                        .entry((&notation.syntax, notation.priority))
                        .or_default()
                        .push((scope_name, notation));
                }
            }
        }
        for entries in by_syntax.values() {
            if entries.len() < 2 {
                continue;
            }
            let first = &entries[0];
            for other in &entries[1..] {
                if first.1.qualified_name != other.1.qualified_name {
                    self.stat_conflicts.set(self.stat_conflicts.get() + 1);
                    errors.push(NotationScopeError::Conflict {
                        scope: first.0.clone(),
                        syntax: first.1.syntax.clone(),
                        first: first.1.qualified_name.clone(),
                        second: other.1.qualified_name.clone(),
                    });
                }
            }
        }
        errors
    }

    /// Export all notations from `source` into `target`. Returns count.
    pub(crate) fn export_scope(
        &mut self,
        source: &Name,
        target: &Name,
    ) -> Result<usize, NotationScopeError> {
        if !self.scopes.contains_key(source) {
            return Err(NotationScopeError::ImportSourceNotFound(source.clone()));
        }
        if !self.scopes.contains_key(target) {
            return Err(NotationScopeError::ExportTargetNotFound(target.clone()));
        }
        let notations: Vec<ScopedNotation> = self
            .scopes
            .get(source)
            .map(|s| s.notations.values().cloned().collect())
            .unwrap_or_default();
        let count = notations.len();
        if let Some(ts) = self.scopes.get_mut(target) {
            for n in notations {
                ts.add_notation(n);
            }
        }
        self.stat_exports.set(self.stat_exports.get() + 1);
        Ok(count)
    }

    /// Import notations from `source` into `target`.
    pub(crate) fn import_scope(
        &mut self,
        target: &Name,
        source: &Name,
    ) -> Result<usize, NotationScopeError> {
        self.export_scope(source, target)
    }

    #[must_use]
    pub(crate) fn stats(&self) -> ScopeStats {
        ScopeStats {
            scopes_defined: self.scopes.len(),
            scopes_active: self.active_stack.len(),
            lookups: self.stat_lookups.get(),
            conflicts: self.stat_conflicts.get(),
            exports: self.stat_exports.get(),
        }
    }

    #[must_use]
    pub(crate) fn scope_count(&self) -> usize {
        self.scopes.len()
    }

    #[must_use]
    pub(crate) fn get_scope(&self, name: &Name) -> Option<&NotationScope> {
        self.scopes.get(name)
    }

    #[must_use]
    pub(crate) fn scope_notations(&self, scope_name: &Name) -> Vec<&ScopedNotation> {
        self.scopes
            .get(scope_name)
            .map(|s| s.notations.values().collect())
            .unwrap_or_default()
    }
}
