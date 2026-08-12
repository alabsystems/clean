// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Namespace manipulation for `open` and `export` commands.
//!
//! In Lean 4, `open Nat in expr` brings names from `Nat` into scope for `expr`,
//! while `open Nat` does so for the rest of the file. `export Nat (add mul)`
//! re-exports selected names from `Nat` into the current namespace.
//!
//! # Architecture
//!
//! [`NamespaceState`] tracks which namespaces are opened and what aliases
//! exist. The elaborator queries it during name resolution via
//! [`NamespaceState::resolve`], which returns the fully-qualified [`Name`]
//! for a short identifier if one is in scope.
//!
//! Scoped opens (`open Foo in ...`) are handled via the scope stack:
//! [`NamespaceState::push_scope`] / [`NamespaceState::pop_scope`].

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::Expr;
use std::collections::HashMap;

/// Errors that can occur during namespace operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum NamespaceError {
    /// The namespace referenced by an `open` or `export` command does not
    /// exist in the environment (no constants have that prefix).
    #[error("unknown namespace: {0}")]
    UnknownNamespace(String),

    /// An `export` command listed a name that does not exist in the source
    /// namespace.
    #[error("name '{name}' not found in namespace '{namespace}'")]
    NameNotFound { namespace: String, name: String },

    /// Attempted to exit a namespace/section when none was active.
    #[error("no active {0} to exit")]
    NoActiveScope(String),

    /// Attempted to exit a named scope with a mismatched name.
    #[error("expected end of {kind} '{expected}', found '{found}'")]
    ScopeMismatch {
        kind: String,
        expected: String,
        found: String,
    },
}

/// A single alias mapping a short name to a fully-qualified name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Alias {
    /// The short name used in source code (e.g., `add`).
    pub(crate) short: String,
    /// The fully-qualified name in the environment (e.g., `Nat.add`).
    pub(crate) target: Name,
}

/// A variable declared within a `section` block via `variable (x : Nat)`.
///
/// Section variables are automatically included as parameters in definitions
/// and theorems within the section that reference them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionVariable {
    /// The variable name (e.g., `x`).
    pub name: Name,
    /// The variable's type expression.
    pub type_: Expr,
    /// How the variable binds: explicit, implicit, instance, etc.
    pub binder_info: BinderInfo,
}

/// A saved frame when entering a `section` block.
///
/// When the section ends, the namespace state is restored to the snapshot
/// captured when the section was entered.
#[derive(Debug, Clone)]
pub struct SectionFrame {
    /// Section name, if given (e.g., `section MySection`). Anonymous
    /// sections have `None`.
    pub name: Option<Name>,
    /// The namespace that was current when this section was opened.
    namespace_at_entry: Name,
    /// Section-scoped variables declared via `variable`.
    variables: Vec<SectionVariable>,
    /// The list of opened namespaces at section entry, for restoration.
    open_namespaces_at_entry: Vec<Name>,
}

/// Tracks opened namespaces, aliases, scope boundaries, and the current
/// namespace/section stack.
///
/// Used by the elaborator during name resolution. When a bare identifier
/// like `add` is encountered, the elaborator calls [`NamespaceState::resolve`]
/// to check whether any open namespace provides a match (e.g., `Nat.add`).
#[derive(Debug, Clone)]
pub struct NamespaceState {
    /// Active aliases: short name -> fully-qualified target.
    /// Multiple opens can map the same short name to different targets;
    /// the last one wins (consistent with Lean 4 shadowing).
    aliases: HashMap<String, Name>,
    /// Scope stack for `open ... in ...` (scoped opens).
    /// Each entry records the number of aliases that existed before the
    /// scope was entered, allowing efficient rollback.
    scope_stack: Vec<ScopeFrame>,
    /// Exported names: maps (current_namespace_prefix + short) -> target.
    /// Populated by `export` commands. These become permanent aliases
    /// visible outside the current file/section.
    exports: Vec<Alias>,
    /// The current namespace prefix (e.g., `Foo.Bar` inside
    /// `namespace Foo / namespace Bar`).
    current_namespace: Name,
    /// Namespaces currently opened via `open` (not scoped `open ... in`).
    /// These are the namespace prefixes themselves (e.g., `Nat`), not the
    /// individual aliases they contribute.
    open_namespaces: Vec<Name>,
    /// Stack of active section frames for `section ... end` scoping.
    section_stack: Vec<SectionFrame>,
}

impl Default for NamespaceState {
    fn default() -> Self {
        Self {
            aliases: HashMap::new(),
            scope_stack: Vec::new(),
            exports: Vec::new(),
            current_namespace: Name::anon(),
            open_namespaces: Vec::new(),
            section_stack: Vec::new(),
        }
    }
}

/// A saved scope frame for scoped opens.
#[derive(Debug, Clone)]
struct ScopeFrame {
    /// Keys that were added in this scope (for rollback).
    added_keys: Vec<String>,
    /// Previous values for keys that were overwritten (for restore).
    overwritten: Vec<(String, Name)>,
    /// Namespaces recorded as opened in this scope via
    /// [`NamespaceState::open_namespace_scoped`] (for rollback of the
    /// `open_namespaces` diagnostic list when the scope ends).
    opened_namespaces: Vec<Name>,
}

impl NamespaceState {
    /// Create an empty namespace state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Resolve a short identifier against opened namespaces.
    ///
    /// Returns the fully-qualified [`Name`] if the identifier matches an
    /// alias from an `open` command, or `None` if no open namespace
    /// provides this name.
    ///
    /// # Example
    ///
    /// After `open Nat`, resolving `"add"` returns `Some(Name("Nat.add"))`.
    #[must_use]
    pub fn resolve(&self, short: &str) -> Option<&Name> {
        self.aliases.get(short)
    }

    /// Check whether any namespaces are currently opened.
    #[must_use]
    pub fn has_opens(&self) -> bool {
        !self.aliases.is_empty()
    }

    /// Return all current aliases (for diagnostics / testing).
    #[must_use]
    pub fn aliases(&self) -> &HashMap<String, Name> {
        &self.aliases
    }

    /// Return all exports (for diagnostics / testing).
    #[must_use]
    // Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
    // production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn exports(&self) -> &[Alias] {
        &self.exports
    }

    /// Push a new scope for `open ... in ...`.
    ///
    /// Aliases added after this call can be rolled back with [`pop_scope`].
    pub fn push_scope(&mut self) {
        self.scope_stack.push(ScopeFrame {
            added_keys: Vec::new(),
            overwritten: Vec::new(),
            opened_namespaces: Vec::new(),
        });
    }

    /// Pop the most recent scope, restoring aliases to their prior state.
    ///
    /// No-op if the scope stack is empty.
    pub fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            // Remove keys that were freshly added in this scope
            for key in &frame.added_keys {
                self.aliases.remove(key);
            }
            // Restore keys that were overwritten
            for (key, old_val) in frame.overwritten {
                self.aliases.insert(key, old_val);
            }
            // Un-record namespaces opened within this scope.
            for ns in frame.opened_namespaces {
                self.open_namespaces.retain(|n| n != &ns);
            }
        }
    }

    /// Insert a single alias, tracking it for scope rollback.
    ///
    /// Public within the crate for use by `namespace_open` module.
    pub(crate) fn insert_alias_pub(&mut self, short: String, target: Name) {
        self.insert_alias(short, target);
    }

    /// Insert an alias that SURVIVES scope pops (`export` semantics).
    ///
    /// Lean records `export` aliases in the environment's permanent alias
    /// table (`Lean/Elab/BuiltinCommand.lean` `elabExport` → `addAlias`), so
    /// an export made inside a `namespace`/`section` block outlives the block.
    /// This bypasses the scope-frame bookkeeping that [`insert_alias_pub`]
    /// uses, so `pop_scope` will not remove the key.
    ///
    /// [`insert_alias_pub`]: Self::insert_alias_pub
    pub(crate) fn insert_alias_unscoped(&mut self, short: String, target: Name) {
        self.aliases.insert(short, target);
    }

    /// Append an export record (used by `namespace_open` module).
    pub(crate) fn push_export(&mut self, alias: Alias) {
        self.exports.push(alias);
    }

    /// Insert a single alias, tracking it for scope rollback.
    fn insert_alias(&mut self, short: String, target: Name) {
        if let Some(frame) = self.scope_stack.last_mut() {
            if let Some(old) = self.aliases.get(&short) {
                frame.overwritten.push((short.clone(), old.clone()));
            } else {
                frame.added_keys.push(short.clone());
            }
        }
        self.aliases.insert(short, target);
    }

    // =========================================================================
    // Namespace management
    // =========================================================================

    /// Get the current namespace prefix.
    ///
    /// Returns `Name::anon()` when at the root namespace.
    #[must_use]
    pub fn current_namespace(&self) -> &Name {
        &self.current_namespace
    }

    /// Enter a namespace, extending the current prefix.
    ///
    /// For example, if the current namespace is `Foo` and we enter `Bar`,
    /// the new namespace becomes `Foo.Bar`.
    pub fn enter_namespace(&mut self, ns: Name) {
        let ns_str = ns.to_string();
        if self.current_namespace.is_anon() {
            self.current_namespace = ns;
        } else {
            let combined = format!("{}.{}", self.current_namespace, ns_str);
            self.current_namespace = Name::from_string(&combined);
        }
    }

    /// Exit the current namespace, restoring the parent prefix.
    ///
    /// For example, if the current namespace is `Foo.Bar`, exiting yields
    /// `Foo`. If the current namespace is a single component like `Foo`,
    /// exiting yields the root (anonymous) namespace.
    pub fn exit_namespace(&mut self) {
        let s = self.current_namespace.to_string();
        if let Some(dot_pos) = s.rfind('.') {
            self.current_namespace = Name::from_string(&s[..dot_pos]);
        } else {
            self.current_namespace = Name::anon();
        }
    }

    // =========================================================================
    // Open namespace tracking
    // =========================================================================

    /// Get the list of currently opened namespaces.
    #[must_use]
    pub fn open_namespaces(&self) -> &[Name] {
        &self.open_namespaces
    }

    /// Record that a namespace has been opened (for name resolution).
    ///
    /// This tracks the namespace prefix itself, separate from the individual
    /// aliases that `process_open` creates.
    pub fn open_namespace(&mut self, ns: Name) {
        if !self.open_namespaces.contains(&ns) {
            self.open_namespaces.push(ns);
        }
    }

    /// Record an opened namespace WITH scope rollback: when the innermost
    /// alias scope (a `namespace`/`section` block or `open … in`) pops, the
    /// record is removed again. Used by simple `open` processing so
    /// diagnostics ("`x` is protected; use `Foo.x`") only fire while the open
    /// is actually in force.
    pub(crate) fn open_namespace_scoped(&mut self, ns: Name) {
        if self.open_namespaces.contains(&ns) {
            return;
        }
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.opened_namespaces.push(ns.clone());
        }
        self.open_namespaces.push(ns);
    }

    /// Remove a namespace from the open list.
    pub fn close_namespace(&mut self, ns: &Name) {
        self.open_namespaces.retain(|n| n != ns);
    }

    // =========================================================================
    // Section management
    // =========================================================================

    /// Enter a new section, saving current state for later restoration.
    ///
    /// `name` is `Some` for named sections (`section Foo`) and `None` for
    /// anonymous sections (`section`).
    pub fn enter_section(&mut self, name: Option<Name>) {
        self.section_stack.push(SectionFrame {
            name,
            namespace_at_entry: self.current_namespace.clone(),
            variables: Vec::new(),
            open_namespaces_at_entry: self.open_namespaces.clone(),
        });
    }

    /// Exit the most recent section, restoring namespace and open state.
    ///
    /// Returns `Err` if no section is active.
    pub fn exit_section(&mut self) -> Result<(), NamespaceError> {
        let frame = self
            .section_stack
            .pop()
            .ok_or_else(|| NamespaceError::NoActiveScope("section".to_string()))?;
        self.current_namespace = frame.namespace_at_entry;
        self.open_namespaces = frame.open_namespaces_at_entry;
        Ok(())
    }

    /// Add a section variable to the current (innermost) section.
    ///
    /// No-op if no section is active (variables declared outside sections
    /// are file-scoped and tracked by `FileContext`).
    pub fn add_section_variable(&mut self, var: SectionVariable) {
        if let Some(frame) = self.section_stack.last_mut() {
            frame.variables.push(var);
        }
    }

    /// Get all section variables from all active section frames,
    /// innermost last.
    ///
    /// Variables from outer sections appear before variables from inner
    /// sections, matching Lean 4's scoping behavior.
    #[must_use]
    pub fn get_section_variables(&self) -> Vec<&SectionVariable> {
        self.section_stack
            .iter()
            .flat_map(|frame| frame.variables.iter())
            .collect()
    }

    /// Get the current section depth (number of active sections).
    #[must_use]
    pub fn section_depth(&self) -> usize {
        self.section_stack.len()
    }

    /// Check whether we are inside a section.
    #[must_use]
    pub fn in_section(&self) -> bool {
        !self.section_stack.is_empty()
    }

    /// Resolve a short name against the current namespace, returning the
    /// qualified form.
    ///
    /// If the current namespace is non-anonymous, prepends it. Otherwise
    /// returns the name unchanged.
    #[must_use]
    pub fn resolve_name(&self, short: &Name) -> Name {
        let short_str = short.to_string();
        if !self.current_namespace.is_anon() {
            let qualified_str = format!("{}.{}", self.current_namespace, short_str);
            return Name::from_string(&qualified_str);
        }
        short.clone()
    }
}

// Re-export open/export processing from the split-out module for backward
// compatibility. All call sites use `crate::namespace::process_open` etc.
pub use crate::namespace_open::{process_export, process_open};

#[cfg(test)]
#[path = "namespace_tests.rs"]
mod tests;
