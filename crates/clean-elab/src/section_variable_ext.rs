// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended section variable handling with dependency tracking and include/omit.
//!
//! Builds on [`SectionScope`](crate::section_scope::SectionScope) with:
//!
//! - **Dependency tracking**: record which declarations reference which
//!   section variables so that the closure operation at `end section` can
//!   generalize only the variables actually used.
//! - **Universe variable scoping**: `universe u` within a section is scoped
//!   to that section and injected into declarations that reference it.
//! - **Include/omit directives**: fine-grained control over which section
//!   variables are auto-included in subsequent declarations.
//! - **Variable shadowing detection**: warn when a local binding shadows a
//!   section variable.
//! - **Nested section support**: sections within sections with correct
//!   variable visibility and scope restoration on `end`.
//! - **Section end processing**: generalize declarations with Pi/Lambda
//!   abstractions for the section variables they used.
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Elab/Command.lean` — `elabSection`, `elabEnd`,
//! `includeUsedSectionVars`, `elabVariable`, `elabIncludeCmd`, `elabOmitCmd`.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::visitor::ExprVisitor;
use clean_kernel::expr::LevelVec;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::section_scope::{
    abstract_section_variables, abstract_section_variables_lam, SectionScope, SectionVariable,
};

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

/// Diagnostic produced during section variable processing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SectionDiagnostic {
    pub(crate) kind: SectionDiagnosticKind,
    pub(crate) message: String,
}

/// Classification of section-variable diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SectionDiagnosticKind {
    /// A local binding shadows a section variable.
    ShadowWarning,
    /// Include/omit targets a name that is not a section variable.
    UnknownVariable,
    /// A section variable is declared with the same name as an existing one.
    DuplicateVariable,
    /// A universe parameter name collides with an existing one.
    DuplicateUniverse,
}

// ---------------------------------------------------------------------------
// Dependency record
// ---------------------------------------------------------------------------

/// Tracks which section variables and universe parameters a single
/// declaration depends on.
#[derive(Debug, Clone, Default)]
pub(crate) struct DeclDependency {
    /// Section variable names used by the declaration.
    pub(crate) variables: Vec<String>,
    /// Universe parameter names used by the declaration.
    pub(crate) universes: Vec<String>,
}

// ---------------------------------------------------------------------------
// Section variable extension
// ---------------------------------------------------------------------------

/// Extended section variable manager with dependency tracking.
///
/// Wraps a stack of [`SectionScope`] values (one per nesting level) and
/// maintains a per-declaration dependency map so that section-end
/// generalization only abstracts over the variables actually used.
#[derive(Debug, Clone)]
pub(crate) struct SectionVariableExt {
    /// Stack of section scopes, innermost last.
    scopes: Vec<SectionScope>,
    /// Section names, parallel to `scopes` (empty string for anonymous).
    section_names: Vec<String>,
    /// Per-declaration dependency record, keyed by declaration name.
    dependencies: HashMap<String, DeclDependency>,
    /// Accumulated diagnostics.
    diagnostics: Vec<SectionDiagnostic>,
}

impl Default for SectionVariableExt {
    fn default() -> Self {
        Self::new()
    }
}

impl SectionVariableExt {
    /// Create a new section variable extension with no active scopes.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            scopes: Vec::new(),
            section_names: Vec::new(),
            dependencies: HashMap::new(),
            diagnostics: Vec::new(),
        }
    }

    // -- Scope management ---------------------------------------------------

    /// Enter a new section scope.
    ///
    /// # ENSURES
    /// - A new `SectionScope` is pushed onto the scope stack
    /// - The section name is recorded (empty for anonymous sections)
    pub(crate) fn enter_section(&mut self, name: &str) {
        self.scopes.push(SectionScope::new());
        self.section_names.push(name.to_owned());
    }

    /// Leave the current section scope and return the scope that was closed.
    ///
    /// # ENSURES
    /// - The innermost scope is popped
    /// - Returns `None` if no section is active
    #[must_use]
    pub(crate) fn leave_section(&mut self) -> Option<SectionScope> {
        self.section_names.pop();
        self.scopes.pop()
    }

    /// Current nesting depth (0 = no active section).
    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// Whether any section is currently active.
    #[must_use]
    pub(crate) fn is_in_section(&self) -> bool {
        !self.scopes.is_empty()
    }

    /// Name of the innermost active section, or `None`.
    #[must_use]
    pub(crate) fn current_section_name(&self) -> Option<&str> {
        self.section_names.last().map(String::as_str)
    }

    // -- Variable management ------------------------------------------------

    /// Add a section variable to the innermost scope.
    ///
    /// Returns a diagnostic if the variable name duplicates an existing one
    /// in any active scope.
    pub(crate) fn add_variable(&mut self, var: SectionVariable) {
        if self.find_variable(&var.name).is_some() {
            self.diagnostics.push(SectionDiagnostic {
                kind: SectionDiagnosticKind::DuplicateVariable,
                message: format!(
                    "section variable '{}' shadows an existing section variable",
                    var.name
                ),
            });
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.add_variable(var);
        }
    }

    /// Add a universe parameter to the innermost scope.
    pub(crate) fn add_universe_param(&mut self, name: &str) {
        if self.all_universe_params().iter().any(|u| u == name) {
            self.diagnostics.push(SectionDiagnostic {
                kind: SectionDiagnosticKind::DuplicateUniverse,
                message: format!(
                    "universe parameter '{}' already declared in an enclosing section",
                    name
                ),
            });
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.add_universe_param(name.to_owned());
        }
    }

    /// Find a section variable by name across all active scopes
    /// (innermost first).
    #[must_use]
    pub(crate) fn find_variable(&self, name: &str) -> Option<&SectionVariable> {
        for scope in self.scopes.iter().rev() {
            for var in scope.all_variables() {
                if var.name == name {
                    return Some(var);
                }
            }
        }
        None
    }

    /// Collect all currently visible section variables across all scopes,
    /// in declaration order (outermost first).
    #[must_use]
    pub(crate) fn all_visible_variables(&self) -> Vec<&SectionVariable> {
        let mut result = Vec::new();
        for scope in &self.scopes {
            for var in scope.all_variables() {
                result.push(var);
            }
        }
        result
    }

    /// Collect all currently included section variables across all scopes.
    #[must_use]
    pub(crate) fn all_included_variables(&self) -> Vec<&SectionVariable> {
        let mut result = Vec::new();
        for scope in &self.scopes {
            for var in scope.included_variables() {
                result.push(var);
            }
        }
        result
    }

    /// Collect all universe parameters from all active scopes
    /// (outermost first).
    #[must_use]
    pub(crate) fn all_universe_params(&self) -> Vec<String> {
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        for scope in &self.scopes {
            for u in scope.universe_params() {
                if seen.insert(u.clone()) {
                    result.push(u.clone());
                }
            }
        }
        result
    }

    // -- Include / omit -----------------------------------------------------

    /// Omit a variable from auto-inclusion in the innermost scope.
    ///
    /// Returns a diagnostic if the name is not a known section variable.
    pub(crate) fn omit_variable(&mut self, name: &str) {
        if self.find_variable(name).is_none() {
            self.diagnostics.push(SectionDiagnostic {
                kind: SectionDiagnosticKind::UnknownVariable,
                message: format!("omit: '{}' is not a section variable in scope", name),
            });
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.omit_variable(name);
        }
    }

    /// Re-include a previously omitted variable in the innermost scope.
    ///
    /// Returns a diagnostic if the name is not a known section variable.
    pub(crate) fn include_variable(&mut self, name: &str) {
        if self.find_variable(name).is_none() {
            self.diagnostics.push(SectionDiagnostic {
                kind: SectionDiagnosticKind::UnknownVariable,
                message: format!("include: '{}' is not a section variable in scope", name),
            });
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.include_variable(name);
        }
    }

    /// Check if a variable is currently included across all scopes.
    ///
    /// A variable is included if it is not omitted in the innermost scope
    /// that declares or controls it.
    #[must_use]
    pub(crate) fn is_included(&self, name: &str) -> bool {
        // Check innermost scope first for include/omit overrides
        for scope in self.scopes.iter().rev() {
            if scope.omitted_names().contains(name) {
                return false;
            }
            // If the variable is in this scope's variables, it's included
            if scope.all_variables().iter().any(|v| v.name == name) {
                return true;
            }
        }
        // Not found in any scope — default to included (for unknown names)
        true
    }

    // -- Shadowing detection ------------------------------------------------

    /// Check whether a local binding name shadows a section variable.
    ///
    /// If so, emits a diagnostic and returns `true`.
    pub(crate) fn check_shadow(&mut self, local_name: &str) -> bool {
        if self.find_variable(local_name).is_some() {
            self.diagnostics.push(SectionDiagnostic {
                kind: SectionDiagnosticKind::ShadowWarning,
                message: format!("local binding '{}' shadows section variable", local_name),
            });
            return true;
        }
        false
    }

    // -- Dependency tracking ------------------------------------------------

    /// Analyze an expression to determine which section variables and
    /// universe parameters it references, and record the result.
    ///
    /// # ENSURES
    /// - The dependency record for `decl_name` is updated
    pub(crate) fn record_dependencies(&mut self, decl_name: &str, expr: &Expr) {
        let referenced_names = collect_const_names_set(expr);
        let mut dep = DeclDependency::default();

        for scope in &self.scopes {
            for var in scope.all_variables() {
                if scope.is_included(&var.name) && referenced_names.contains(var.name.as_str()) {
                    dep.variables.push(var.name.clone());
                }
            }
        }

        // Universe parameters referenced in the expression
        let all_univs = self.all_universe_params();
        for u in &all_univs {
            if referenced_names.contains(u.as_str()) {
                dep.universes.push(u.clone());
            }
        }

        self.dependencies.insert(decl_name.to_owned(), dep);
    }

    /// Retrieve the dependency record for a declaration.
    #[must_use]
    pub(crate) fn get_dependency(&self, decl_name: &str) -> Option<&DeclDependency> {
        self.dependencies.get(decl_name)
    }

    // -- Section end processing ---------------------------------------------

    /// Generalize a declaration type by abstracting over used section
    /// variables (Pi abstraction for types).
    ///
    /// Only includes variables that `decl_name` actually depends on.
    pub(crate) fn generalize_type(&self, decl_name: &str, ty: &Expr) -> Expr {
        let vars = self.used_variables_for(decl_name);
        let refs: Vec<&SectionVariable> = vars.iter().collect();
        abstract_section_variables(ty, &refs)
    }

    /// Generalize a declaration body by abstracting over used section
    /// variables (Lambda abstraction for values).
    ///
    /// Only includes variables that `decl_name` actually depends on.
    pub(crate) fn generalize_value(&self, decl_name: &str, val: &Expr) -> Expr {
        let vars = self.used_variables_for(decl_name);
        let refs: Vec<&SectionVariable> = vars.iter().collect();
        abstract_section_variables_lam(val, &refs)
    }

    /// Collect universe parameters that `decl_name` depends on.
    #[must_use]
    pub(crate) fn used_universes_for(&self, decl_name: &str) -> Vec<String> {
        self.dependencies
            .get(decl_name)
            .map(|d| d.universes.clone())
            .unwrap_or_default()
    }

    // -- Diagnostics --------------------------------------------------------

    /// Take all accumulated diagnostics, draining the internal buffer.
    pub(crate) fn take_diagnostics(&mut self) -> Vec<SectionDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Read all diagnostics without consuming them.
    #[must_use]
    pub(crate) fn diagnostics(&self) -> &[SectionDiagnostic] {
        &self.diagnostics
    }

    // -- Private helpers ----------------------------------------------------

    /// Collect the section variables that `decl_name` depends on, in
    /// declaration order (outermost scope first).
    fn used_variables_for(&self, decl_name: &str) -> Vec<SectionVariable> {
        let dep = match self.dependencies.get(decl_name) {
            Some(d) => d,
            None => return Vec::new(),
        };
        let dep_set: HashSet<&str> = dep.variables.iter().map(String::as_str).collect();
        let mut result = Vec::new();
        for scope in &self.scopes {
            for var in scope.all_variables() {
                if dep_set.contains(var.name.as_str()) {
                    result.push(var.clone());
                }
            }
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Free name collection (set-based for O(1) lookup)
// ---------------------------------------------------------------------------

/// Visitor that collects all constant name strings from an expression.
struct ConstNameSetCollector {
    names: HashSet<String>,
}

impl ExprVisitor for ConstNameSetCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.names.insert(name.to_string());
    }
}

/// Collect all constant names referenced in a kernel expression as a set.
fn collect_const_names_set(expr: &Expr) -> HashSet<String> {
    let mut collector = ConstNameSetCollector {
        names: HashSet::new(),
    };
    collector.visit_expr(expr);
    collector.names
}
