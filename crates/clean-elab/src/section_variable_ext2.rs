// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended section variable handling: auto-inclusion, universe tracking,
//! dependent variable analysis, notation scoping, nesting, end-section
//! generalization, include/omit directives, and fvar-to-bvar substitution.
//!
//! # Lean 4 Reference
//!
//! `src/Lean/Elab/Command.lean` -- `elabSection`, `elabEnd`,
//! `includeUsedSectionVars`, `elabVariable`, `elabIncludeCmd`, `elabOmitCmd`.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::visitor::ExprVisitor;
use clean_kernel::expr::LevelVec;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::section_scope::{
    abstract_section_variables, abstract_section_variables_lam, SectionVariable,
};

/// Errors from extended section variable operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum SectionVarExt2Error {
    #[error("no section is currently open")]
    NoOpenSection,
    #[error("section name mismatch: expected '{expected}', got '{actual}'")]
    NameMismatch { expected: String, actual: String },
    #[error("'{0}' is not a section variable in scope")]
    UnknownVariable(String),
    #[error("section variable '{0}' already declared")]
    DuplicateVariable(String),
}

/// A notation whose lifetime is scoped to a section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopedNotation {
    pub(crate) pattern: String,
    pub(crate) expansion: String,
    pub(crate) referenced_vars: Vec<String>,
}

/// Cumulative statistics for section variable operations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SectionVarStats {
    pub(crate) vars_included: usize,
    pub(crate) vars_generalized: usize,
    pub(crate) vars_omitted: usize,
    pub(crate) max_depth: usize,
}

/// State for a single section nesting level.
#[derive(Debug, Clone)]
struct ScopeLevel {
    name: String,
    variables: Vec<SectionVariable>,
    universe_params: Vec<String>,
    omits: HashSet<String>,
    notations: Vec<ScopedNotation>,
}

impl ScopeLevel {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            variables: Vec::new(),
            universe_params: Vec::new(),
            omits: HashSet::new(),
            notations: Vec::new(),
        }
    }

    fn is_included(&self, var_name: &str) -> bool {
        !self.omits.contains(var_name)
    }
}

/// Extended section variable manager with auto-inclusion, dependent variable
/// analysis, notation scoping, and fvar substitution.
#[derive(Debug, Clone)]
pub(crate) struct SectionVariableExt2 {
    scopes: Vec<ScopeLevel>,
    dependencies: HashMap<String, HashSet<String>>,
    universe_deps: HashMap<String, HashSet<String>>,
    stats: SectionVarStats,
}

impl Default for SectionVariableExt2 {
    fn default() -> Self {
        Self::new()
    }
}

impl SectionVariableExt2 {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            scopes: Vec::new(),
            dependencies: HashMap::new(),
            universe_deps: HashMap::new(),
            stats: SectionVarStats::default(),
        }
    }

    // -- Scope management ---------------------------------------------------

    pub(crate) fn enter_section(&mut self, name: &str) {
        self.scopes.push(ScopeLevel::new(name));
        if self.scopes.len() > self.stats.max_depth {
            self.stats.max_depth = self.scopes.len();
        }
    }

    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.scopes.len()
    }

    #[must_use]
    pub(crate) fn is_in_section(&self) -> bool {
        !self.scopes.is_empty()
    }

    #[must_use]
    pub(crate) fn current_section_name(&self) -> Option<&str> {
        self.scopes.last().map(|s| s.name.as_str())
    }

    // -- Variable management ------------------------------------------------

    pub(crate) fn add_variable(&mut self, var: SectionVariable) -> Result<(), SectionVarExt2Error> {
        if self.find_variable(&var.name).is_some() {
            return Err(SectionVarExt2Error::DuplicateVariable(var.name.clone()));
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.variables.push(var);
        }
        Ok(())
    }

    pub(crate) fn add_universe_param(&mut self, name: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.universe_params.push(name.to_owned());
        }
    }

    #[must_use]
    pub(crate) fn find_variable(&self, name: &str) -> Option<&SectionVariable> {
        for scope in self.scopes.iter().rev() {
            for var in &scope.variables {
                if var.name == name {
                    return Some(var);
                }
            }
        }
        None
    }

    #[must_use]
    pub(crate) fn all_visible_variables(&self) -> Vec<&SectionVariable> {
        self.scopes
            .iter()
            .flat_map(|s| s.variables.iter())
            .collect()
    }

    #[must_use]
    pub(crate) fn all_universe_params(&self) -> Vec<String> {
        let mut seen = HashSet::new();
        self.scopes
            .iter()
            .flat_map(|s| s.universe_params.iter())
            .filter(|u| seen.insert(u.as_str().to_owned()))
            .cloned()
            .collect()
    }

    // -- Include / omit -----------------------------------------------------

    pub(crate) fn omit_variable(&mut self, name: &str) -> Result<(), SectionVarExt2Error> {
        if self.find_variable(name).is_none() {
            return Err(SectionVarExt2Error::UnknownVariable(name.to_owned()));
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.omits.insert(name.to_owned());
        }
        self.stats.vars_omitted += 1;
        Ok(())
    }

    pub(crate) fn include_variable(&mut self, name: &str) -> Result<(), SectionVarExt2Error> {
        if self.find_variable(name).is_none() {
            return Err(SectionVarExt2Error::UnknownVariable(name.to_owned()));
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.omits.remove(name);
        }
        Ok(())
    }

    #[must_use]
    pub(crate) fn is_included(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.omits.contains(name) {
                return false;
            }
        }
        true
    }

    // -- Notation scoping ---------------------------------------------------

    pub(crate) fn add_notation(&mut self, notation: ScopedNotation) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.notations.push(notation);
        }
    }

    #[must_use]
    pub(crate) fn all_notations(&self) -> Vec<&ScopedNotation> {
        self.scopes
            .iter()
            .flat_map(|s| s.notations.iter())
            .collect()
    }

    // -- Dependent variable analysis ----------------------------------------

    /// Compute the transitive dependency closure for a set of variable names.
    /// If variable `x` has type referencing section variable `α`, including `x`
    /// forces inclusion of `α`.
    #[must_use]
    pub(crate) fn dependency_closure(&self, initial: &HashSet<String>) -> HashSet<String> {
        let mut result = initial.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for scope in &self.scopes {
                for var in &scope.variables {
                    if !result.contains(&var.name) {
                        continue;
                    }
                    let type_refs = collect_const_names_set(&var.ty);
                    for other_scope in &self.scopes {
                        for other_var in &other_scope.variables {
                            if !result.contains(&other_var.name)
                                && type_refs.contains(&other_var.name)
                            {
                                result.insert(other_var.name.clone());
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        result
    }

    // -- Auto-inclusion (dependency recording) ------------------------------

    /// Analyze an expression and record which section variables and universe
    /// params it uses, expanding the dependency closure.
    pub(crate) fn record_auto_inclusion(&mut self, decl_name: &str, expr: &Expr) {
        let referenced = collect_const_names_set(expr);
        let mut direct_vars: HashSet<String> = HashSet::new();
        let mut direct_univs: HashSet<String> = HashSet::new();
        for scope in &self.scopes {
            for var in &scope.variables {
                if scope.is_included(&var.name) && referenced.contains(&var.name) {
                    direct_vars.insert(var.name.clone());
                }
            }
            for u in &scope.universe_params {
                if referenced.contains(u) {
                    direct_univs.insert(u.clone());
                }
            }
        }
        let closed_vars = self.dependency_closure(&direct_vars);
        // Collect universe params from types of included variables.
        for scope in &self.scopes {
            for var in &scope.variables {
                if closed_vars.contains(&var.name) {
                    let type_refs = collect_const_names_set(&var.ty);
                    for u in &scope.universe_params {
                        if type_refs.contains(u) {
                            direct_univs.insert(u.clone());
                        }
                    }
                }
            }
        }
        self.stats.vars_included += closed_vars.len();
        self.dependencies.insert(decl_name.to_owned(), closed_vars);
        self.universe_deps
            .insert(decl_name.to_owned(), direct_univs);
    }

    #[must_use]
    pub(crate) fn get_variable_deps(&self, decl_name: &str) -> Option<&HashSet<String>> {
        self.dependencies.get(decl_name)
    }

    #[must_use]
    pub(crate) fn get_universe_deps(&self, decl_name: &str) -> Option<&HashSet<String>> {
        self.universe_deps.get(decl_name)
    }

    // -- End-section generalization -----------------------------------------

    /// Close the current section, returning generalization data.
    pub(crate) fn end_section(
        &mut self,
        expected_name: &str,
    ) -> Result<EndSectionResult, SectionVarExt2Error> {
        let scope = self
            .scopes
            .last()
            .ok_or(SectionVarExt2Error::NoOpenSection)?;
        if !expected_name.is_empty() && !scope.name.is_empty() && scope.name != expected_name {
            return Err(SectionVarExt2Error::NameMismatch {
                expected: scope.name.clone(),
                actual: expected_name.to_owned(),
            });
        }
        let scope = self.scopes.pop().expect("checked above");
        Ok(EndSectionResult {
            name: scope.name,
            closed_variables: scope.variables,
            closed_universes: scope.universe_params,
            expired_notations: scope.notations,
        })
    }

    /// Generalize a type (Pi binders) over section variables `decl_name` uses.
    pub(crate) fn generalize_type(&self, decl_name: &str, ty: &Expr) -> Expr {
        let vars = self.ordered_deps_for(decl_name);
        let refs: Vec<&SectionVariable> = vars.iter().collect();
        abstract_section_variables(ty, &refs)
    }

    /// Generalize a value (Lambda binders) over section variables `decl_name` uses.
    pub(crate) fn generalize_value(&self, decl_name: &str, val: &Expr) -> Expr {
        let vars = self.ordered_deps_for(decl_name);
        let refs: Vec<&SectionVariable> = vars.iter().collect();
        abstract_section_variables_lam(val, &refs)
    }

    // -- Fvar substitution --------------------------------------------------

    /// Replace `Expr::const(name)` matching a section variable name with
    /// `Expr::bvar(idx)` using de Bruijn indices relative to generalization
    /// binders.
    pub(crate) fn substitute_fvars(&self, decl_name: &str, expr: &Expr) -> Expr {
        let vars = self.ordered_deps_for(decl_name);
        if vars.is_empty() {
            return expr.clone();
        }
        let count = vars.len() as u32;
        let mut name_to_idx: HashMap<String, u32> = HashMap::new();
        for (i, var) in vars.iter().enumerate() {
            name_to_idx.insert(var.name.clone(), count - 1 - i as u32);
        }
        substitute_const_with_bvar(expr, &name_to_idx)
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &SectionVarStats {
        &self.stats
    }

    // -- Private helpers ----------------------------------------------------

    fn ordered_deps_for(&self, decl_name: &str) -> Vec<SectionVariable> {
        let dep_set = match self.dependencies.get(decl_name) {
            Some(s) => s,
            None => return Vec::new(),
        };
        self.scopes
            .iter()
            .flat_map(|s| s.variables.iter())
            .filter(|v| dep_set.contains(&v.name))
            .cloned()
            .collect()
    }
}

/// Data returned when a section is closed.
#[derive(Debug, Clone)]
pub(crate) struct EndSectionResult {
    pub(crate) name: String,
    pub(crate) closed_variables: Vec<SectionVariable>,
    pub(crate) closed_universes: Vec<String>,
    pub(crate) expired_notations: Vec<ScopedNotation>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn collect_const_names_set(expr: &Expr) -> HashSet<String> {
    let mut c = ConstNameSetCollector {
        names: HashSet::new(),
    };
    c.visit_expr(expr);
    c.names
}

/// Replace `Expr::Const(name, _)` with `Expr::bvar(idx)` per substitution map.
fn substitute_const_with_bvar(expr: &Expr, map: &HashMap<String, u32>) -> Expr {
    use clean_kernel::expr::ExprKind;
    match expr.kind() {
        ExprKind::Const(name, _) => {
            if let Some(&idx) = map.get(&name.to_string()) {
                Expr::bvar(idx)
            } else {
                expr.clone()
            }
        }
        ExprKind::App(f, a) => Expr::app(
            substitute_const_with_bvar(f, map),
            substitute_const_with_bvar(a, map),
        ),
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            substitute_const_with_bvar(ty, map),
            substitute_const_with_bvar(body, map),
        ),
        ExprKind::Pi(bd, ty, body) => Expr::pi(
            *bd,
            substitute_const_with_bvar(ty, map),
            substitute_const_with_bvar(body, map),
        ),
        _ => expr.clone(),
    }
}
