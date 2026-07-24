// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Section-level variable scoping with include/omit control.
//!
//! In Lean 4, `section ... end` blocks define scopes where `variable`
//! declarations accumulate. The `include` and `omit` commands control which
//! section variables are automatically included in subsequent declarations.
//!
//! # Example
//!
//! ```text
//! section Foo
//!   variable (n : Nat)
//!   variable {m : Nat}
//!   omit n            -- don't auto-include n
//!   def bar : Nat := m  -- only m is auto-included (n is omitted)
//!   include n         -- re-include n
//!   def baz : Nat := n + m  -- both n and m are auto-included
//! end Foo
//! ```
//!
//! # Architecture
//!
//! [`SectionScope`] tracks the variables, universe parameters, and include/omit
//! state within a single section. [`resolve_section_variables`] performs free
//! variable analysis to determine which section variables a declaration uses.
//! [`abstract_section_variables`] wraps an expression with binders for the
//! resolved variables.
//!
//! # Lean 4 Reference
//!
//! See `src/Lean/Elab/Command.lean` -- `elabVariable`, `elabIncludeCmd`,
//! `elabOmitCmd`, and `includeUsedSectionVars`.

use std::collections::HashSet;

use clean_kernel::expr::visitor::ExprVisitor;
use clean_kernel::expr::{BinderInfo, LevelVec};
use clean_kernel::name::Name;
use clean_kernel::Expr;

/// A single section variable declaration.
///
/// Represents one variable from a `variable` command within a section.
/// Each variable has a name, type, binder info, and whether it is implicit.
#[derive(Debug, Clone)]
pub(crate) struct SectionVariable {
    /// The variable name (e.g., `n`, `alpha`).
    pub(crate) name: String,
    /// The kernel type of the variable.
    pub(crate) ty: Expr,
    /// How the variable binds: explicit `(x : T)`, implicit `{x : T}`,
    /// or instance `[x : T]`.
    pub(crate) binder_info: BinderInfo,
    /// Whether the variable was declared with implicit syntax.
    /// Redundant with `binder_info == Implicit` in most cases, but kept
    /// for compatibility with Lean 4's internal representation where
    /// `is_implicit` may differ from binder info for strict implicit.
    pub(crate) is_implicit: bool,
}

impl SectionVariable {
    /// Create a new section variable.
    #[must_use]
    pub(crate) fn new(name: String, ty: Expr, binder_info: BinderInfo) -> Self {
        let is_implicit = matches!(
            binder_info,
            BinderInfo::Implicit | BinderInfo::StrictImplicit
        );
        Self {
            name,
            ty,
            binder_info,
            is_implicit,
        }
    }

    /// Create a new explicit section variable.
    #[must_use]
    pub(crate) fn explicit(name: String, ty: Expr) -> Self {
        Self::new(name, ty, BinderInfo::Default)
    }

    /// Create a new implicit section variable.
    #[must_use]
    pub(crate) fn implicit(name: String, ty: Expr) -> Self {
        Self::new(name, ty, BinderInfo::Implicit)
    }

    /// Create a new instance-implicit section variable.
    #[must_use]
    pub(crate) fn inst_implicit(name: String, ty: Expr) -> Self {
        Self::new(name, ty, BinderInfo::InstImplicit)
    }
}

/// Section-level scope tracking with include/omit control.
///
/// A `SectionScope` is created when entering a `section ... end` block and
/// accumulates variable declarations, universe parameters, and include/omit
/// state within that scope.
///
/// Variables are auto-included by default. The `omit` command excludes a
/// variable from automatic inclusion, and `include` re-includes it.
#[derive(Debug, Clone)]
pub(crate) struct SectionScope {
    /// Variables declared within this section scope.
    pub(crate) variables: Vec<SectionVariable>,
    /// Universe parameter names declared in this section.
    pub(crate) universe_params: Vec<String>,
    /// Variables that have been explicitly included (overrides omit).
    includes: HashSet<String>,
    /// Variables that have been explicitly omitted from auto-inclusion.
    omits: HashSet<String>,
}

impl Default for SectionScope {
    fn default() -> Self {
        Self::new()
    }
}

impl SectionScope {
    /// Create a new empty section scope.
    ///
    /// # ENSURES
    /// - No variables, universe params, includes, or omits
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            variables: Vec::new(),
            universe_params: Vec::new(),
            includes: HashSet::new(),
            omits: HashSet::new(),
        }
    }

    /// Add a variable to this section scope.
    ///
    /// Variables are auto-included by default unless later omitted.
    ///
    /// # ENSURES
    /// - Variable is appended to the variables list
    pub(crate) fn add_variable(&mut self, var: SectionVariable) {
        self.variables.push(var);
    }

    /// Add a universe parameter to this section scope.
    ///
    /// # ENSURES
    /// - Parameter name is appended to the universe params list
    pub(crate) fn add_universe_param(&mut self, name: String) {
        self.universe_params.push(name);
    }

    /// Omit a variable from automatic inclusion.
    ///
    /// After this call, the named variable will not be auto-included in
    /// declarations unless explicitly `include`d again.
    ///
    /// # ENSURES
    /// - Variable is in the omits set
    /// - Variable is removed from includes set (if present)
    /// - `is_included(name)` returns `false`
    pub(crate) fn omit_variable(&mut self, name: &str) {
        self.omits.insert(name.to_owned());
        self.includes.remove(name);
    }

    /// Re-include a previously omitted variable.
    ///
    /// After this call, the named variable will be eligible for automatic
    /// inclusion in declarations again.
    ///
    /// # ENSURES
    /// - Variable is removed from the omits set
    /// - Variable is in the includes set
    /// - `is_included(name)` returns `true`
    pub(crate) fn include_variable(&mut self, name: &str) {
        self.omits.remove(name);
        self.includes.insert(name.to_owned());
    }

    /// Check if a variable is currently included (eligible for auto-binding).
    ///
    /// A variable is included if it has NOT been omitted, OR if it has been
    /// explicitly re-included after being omitted.
    ///
    /// # ENSURES
    /// - Returns `true` if the variable should be auto-included
    #[must_use]
    pub(crate) fn is_included(&self, name: &str) -> bool {
        !self.omits.contains(name)
    }

    /// Get all variables that are currently included (not omitted).
    ///
    /// # ENSURES
    /// - Returns variables in declaration order, filtered by include state
    #[must_use]
    pub(crate) fn included_variables(&self) -> Vec<&SectionVariable> {
        self.variables
            .iter()
            .filter(|v| self.is_included(&v.name))
            .collect()
    }

    /// Get all variables in this scope (regardless of include/omit state).
    #[must_use]
    pub(crate) fn all_variables(&self) -> &[SectionVariable] {
        &self.variables
    }

    /// Get the universe parameters declared in this scope.
    #[must_use]
    pub(crate) fn universe_params(&self) -> &[String] {
        &self.universe_params
    }

    /// Get the set of omitted variable names.
    #[must_use]
    pub(crate) fn omitted_names(&self) -> &HashSet<String> {
        &self.omits
    }

    /// Get the number of variables in this scope.
    #[must_use]
    pub(crate) fn variable_count(&self) -> usize {
        self.variables.len()
    }
}

// ---------------------------------------------------------------------------
// Free variable analysis for section variable resolution
// ---------------------------------------------------------------------------

/// Visitor that collects all constant names from an expression.
///
/// Used for detecting which section variables are referenced by a declaration.
struct ConstNameCollector {
    names: Vec<Name>,
}

impl ExprVisitor for ConstNameCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.names.push(name.clone());
    }
}

/// Collect all constant names referenced in a kernel expression.
///
/// Traverses the expression tree and accumulates `Name` values from
/// `Expr::Const` nodes. Deduplicates while preserving first-occurrence order.
fn collect_const_names(expr: &Expr) -> Vec<Name> {
    let mut collector = ConstNameCollector { names: Vec::new() };
    collector.visit_expr(expr);
    let mut seen = HashSet::new();
    collector.names.retain(|n| seen.insert(n.clone()));
    collector.names
}

/// Resolve which section variables are used by an expression.
///
/// Performs free variable analysis on the expression and returns the subset
/// of section variables (in declaration order) whose names appear as constants
/// in the expression. Only variables that are currently included (not omitted)
/// are returned.
///
/// # REQUIRES
/// - `expr` is a well-formed kernel expression
/// - `scope` contains valid section variable declarations
///
/// # ENSURES
/// - Returns section variables that are both:
///   1. Referenced (by name) in the expression
///   2. Currently included (not omitted) in the scope
/// - Variables are returned in declaration order
#[must_use]
pub(crate) fn resolve_section_variables<'a>(
    expr: &Expr,
    scope: &'a SectionScope,
) -> Vec<&'a SectionVariable> {
    let referenced_names = collect_const_names(expr);

    scope
        .variables
        .iter()
        .filter(|var| {
            scope.is_included(&var.name)
                && referenced_names.iter().any(|n| n.to_string() == var.name)
        })
        .collect()
}

/// Abstract section variables from an expression by adding binders.
///
/// Given a kernel expression and a list of resolved section variables, wraps
/// the expression in Pi (forall) binders for each variable, producing a
/// self-contained expression.
///
/// For example, if `vars` contains `{alpha : Type}` and `(n : Nat)`,
/// the expression `List alpha -> Nat` becomes:
/// `{alpha : Type} -> (n : Nat) -> List alpha -> Nat`
///
/// # REQUIRES
/// - `expr` is a well-formed kernel expression
/// - `vars` are valid section variables in the desired binding order
///
/// # ENSURES
/// - Returns expression with one additional outermost Pi binder per variable
/// - Binder info from each variable is preserved
/// - Variable binding order matches `vars` order (first = outermost)
/// - If `vars` is empty, returns `expr` unchanged
pub(crate) fn abstract_section_variables(expr: &Expr, vars: &[&SectionVariable]) -> Expr {
    if vars.is_empty() {
        return expr.clone();
    }

    // Fold right-to-left so the first variable becomes the outermost binder.
    vars.iter().rev().fold(expr.clone(), |inner, var| {
        Expr::pi(var.binder_info, var.ty.clone(), inner)
    })
}

/// Abstract section variables using Lambda binders instead of Pi.
///
/// Same as [`abstract_section_variables`] but wraps with Lambda binders,
/// which is needed for definition bodies (as opposed to types).
///
/// # REQUIRES
/// - `expr` is a well-formed kernel expression
/// - `vars` are valid section variables in the desired binding order
///
/// # ENSURES
/// - Returns expression with one Lambda binder per variable
/// - If `vars` is empty, returns `expr` unchanged
pub(crate) fn abstract_section_variables_lam(expr: &Expr, vars: &[&SectionVariable]) -> Expr {
    if vars.is_empty() {
        return expr.clone();
    }

    vars.iter().rev().fold(expr.clone(), |inner, var| {
        Expr::lam(var.binder_info, var.ty.clone(), inner)
    })
}

#[cfg(test)]
#[path = "section_scope_tests.rs"]
mod tests;
