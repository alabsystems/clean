// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended section scope analysis and visualization.
//!
//! Builds on [`SectionScope`](crate::section_scope::SectionScope) with scope
//! visualization, variable tracking, statistics, diffing, auto-bound analysis,
//! section dependency tracking, and validation.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::section_scope::{SectionScope, SectionVariable};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from section scope validation.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ScopeValidationError {
    #[error("duplicate variable '{name}' in scope at depth {depth}")]
    DuplicateVariable { name: String, depth: usize },
    #[error("scope nesting error: {message}")]
    NestingError { message: String },
    #[error("universe parameter '{name}' collides with variable at depth {depth}")]
    UniverseVariableCollision { name: String, depth: usize },
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// Statistics for a single scope level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeLevelStats {
    pub(crate) depth: usize,
    pub(crate) variable_count: usize,
    pub(crate) included_count: usize,
    pub(crate) omitted_count: usize,
    pub(crate) implicit_count: usize,
    pub(crate) inst_implicit_count: usize,
    pub(crate) explicit_count: usize,
    pub(crate) universe_count: usize,
}

/// Aggregate statistics across a scope stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeStackStats {
    pub(crate) depth: usize,
    pub(crate) total_variables: usize,
    pub(crate) total_included: usize,
    pub(crate) total_universes: usize,
    pub(crate) levels: Vec<ScopeLevelStats>,
}

/// Describes changes between two scope states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeDiff {
    pub(crate) added_variables: Vec<String>,
    pub(crate) removed_variables: Vec<String>,
    pub(crate) toggled_variables: Vec<String>,
    pub(crate) depth_change: i32,
    pub(crate) added_universes: Vec<String>,
    pub(crate) removed_universes: Vec<String>,
}

/// Auto-binding candidacy info for a variable at a scope level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AutoBoundCandidate {
    pub(crate) name: String,
    pub(crate) scope_depth: usize,
    pub(crate) is_included: bool,
    pub(crate) is_implicit: bool,
}

/// Tracks which variables from outer scopes a given scope level references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SectionDependencyInfo {
    pub(crate) scope_depth: usize,
    pub(crate) outer_dependencies: Vec<String>,
    pub(crate) own_variables: Vec<String>,
}

// ---------------------------------------------------------------------------
// Visualization
// ---------------------------------------------------------------------------

/// Generate a tree-format visualization of scope nesting hierarchy.
///
/// Variables annotated as `(x : ...)` (explicit), `{x : ...}` (implicit),
/// `[x : ...]` (instance). Omitted variables marked `-- omitted`.
#[must_use]
pub(crate) fn visualize_scope_tree(scopes: &[SectionScope], section_names: &[&str]) -> String {
    if scopes.is_empty() {
        return String::new();
    }
    let mut out = String::new();
    for (i, scope) in scopes.iter().enumerate() {
        let indent = "  ".repeat(i);
        let name = display_name(section_names.get(i).copied());
        let _ = writeln!(out, "{indent}section {name}");
        let var_indent = "  ".repeat(i + 1);
        for var in scope.all_variables() {
            let _ = writeln!(out, "{var_indent}{}", format_binder(var, scope));
        }
        for u in scope.universe_params() {
            let _ = writeln!(out, "{var_indent}universe {u}");
        }
    }
    for i in (0..scopes.len()).rev() {
        let indent = "  ".repeat(i);
        let name = display_name(section_names.get(i).copied());
        let _ = writeln!(out, "{indent}end {name}");
    }
    out
}

fn display_name(name: Option<&str>) -> &str {
    match name {
        Some(n) if !n.is_empty() => n,
        _ => "<anon>",
    }
}

fn format_binder(var: &SectionVariable, scope: &SectionScope) -> String {
    let suffix = if scope.is_included(&var.name) {
        ""
    } else {
        " -- omitted"
    };
    match var.binder_info {
        clean_kernel::expr::BinderInfo::Default => {
            format!("variable ({} : ...){suffix}", var.name)
        }
        clean_kernel::expr::BinderInfo::Implicit
        | clean_kernel::expr::BinderInfo::StrictImplicit => {
            format!("variable {{{} : ...}}{suffix}", var.name)
        }
        clean_kernel::expr::BinderInfo::InstImplicit => {
            format!("variable [{} : ...]{suffix}", var.name)
        }
    }
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Compute per-level and aggregate statistics for a scope stack.
#[must_use]
pub(crate) fn compute_scope_stats(scopes: &[SectionScope]) -> ScopeStackStats {
    let mut levels = Vec::with_capacity(scopes.len());
    let (mut total_variables, mut total_included, mut total_universes) = (0, 0, 0);

    for (i, scope) in scopes.iter().enumerate() {
        let variable_count = scope.variable_count();
        let included_count = scope.included_variables().len();
        let (mut implicit_count, mut inst_implicit_count, mut explicit_count) = (0, 0, 0);
        for var in scope.all_variables() {
            match var.binder_info {
                clean_kernel::expr::BinderInfo::Implicit
                | clean_kernel::expr::BinderInfo::StrictImplicit => implicit_count += 1,
                clean_kernel::expr::BinderInfo::InstImplicit => inst_implicit_count += 1,
                clean_kernel::expr::BinderInfo::Default => explicit_count += 1,
            }
        }
        let universe_count = scope.universe_params().len();
        total_variables += variable_count;
        total_included += included_count;
        total_universes += universe_count;
        levels.push(ScopeLevelStats {
            depth: i,
            variable_count,
            included_count,
            omitted_count: variable_count - included_count,
            implicit_count,
            inst_implicit_count,
            explicit_count,
            universe_count,
        });
    }
    ScopeStackStats {
        depth: scopes.len(),
        total_variables,
        total_included,
        total_universes,
        levels,
    }
}

/// Find variables declared but never referenced in any other variable's type.
#[must_use]
pub(crate) fn find_unused_variables(scopes: &[SectionScope]) -> Vec<String> {
    let all_names: HashSet<String> = scopes
        .iter()
        .flat_map(|s| s.all_variables().iter().map(|v| v.name.clone()))
        .collect();
    let mut referenced: HashSet<String> = HashSet::new();
    for scope in scopes {
        for var in scope.all_variables() {
            collect_const_names_from_expr(&var.ty, &mut referenced);
        }
    }
    let mut unused: Vec<String> = all_names
        .into_iter()
        .filter(|n| !referenced.contains(n))
        .collect();
    unused.sort();
    unused
}

fn collect_const_names_from_expr(expr: &clean_kernel::Expr, out: &mut HashSet<String>) {
    use clean_kernel::expr::ExprKind;
    match expr.kind() {
        ExprKind::Const(name, _) => {
            out.insert(name.to_string());
        }
        ExprKind::App(f, a) => {
            collect_const_names_from_expr(f, out);
            collect_const_names_from_expr(a, out);
        }
        ExprKind::Pi(_, dom, body) | ExprKind::Lam(_, dom, body) => {
            collect_const_names_from_expr(dom, out);
            collect_const_names_from_expr(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_const_names_from_expr(ty, out);
            collect_const_names_from_expr(val, out);
            collect_const_names_from_expr(body, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            collect_const_names_from_expr(inner, out);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Scope diff
// ---------------------------------------------------------------------------

/// Compute the difference between two scope stack states.
#[must_use]
pub(crate) fn diff_scope_stacks(old: &[SectionScope], new: &[SectionScope]) -> ScopeDiff {
    let old_vars = collect_names(old);
    let new_vars = collect_names(new);
    let old_univs = collect_univs(old);
    let new_univs = collect_univs(new);
    let old_omits = collect_omits(old);
    let new_omits = collect_omits(new);

    ScopeDiff {
        added_variables: new_vars
            .iter()
            .filter(|n| !old_vars.contains(*n))
            .cloned()
            .collect(),
        removed_variables: old_vars
            .iter()
            .filter(|n| !new_vars.contains(*n))
            .cloned()
            .collect(),
        toggled_variables: new_vars
            .intersection(&old_vars)
            .filter(|n| old_omits.contains(*n) != new_omits.contains(*n))
            .cloned()
            .collect(),
        depth_change: new.len() as i32 - old.len() as i32,
        added_universes: new_univs
            .iter()
            .filter(|u| !old_univs.contains(*u))
            .cloned()
            .collect(),
        removed_universes: old_univs
            .iter()
            .filter(|u| !new_univs.contains(*u))
            .cloned()
            .collect(),
    }
}

fn collect_names(scopes: &[SectionScope]) -> HashSet<String> {
    scopes
        .iter()
        .flat_map(|s| s.all_variables().iter().map(|v| v.name.clone()))
        .collect()
}

fn collect_univs(scopes: &[SectionScope]) -> HashSet<String> {
    scopes
        .iter()
        .flat_map(|s| s.universe_params().iter().cloned())
        .collect()
}

fn collect_omits(scopes: &[SectionScope]) -> HashSet<String> {
    scopes
        .iter()
        .flat_map(|s| s.omitted_names().iter().cloned())
        .collect()
}

// ---------------------------------------------------------------------------
// Auto-bound analysis
// ---------------------------------------------------------------------------

/// Analyze which variables are auto-bound candidates at each scope level.
#[must_use]
pub(crate) fn analyze_auto_bound_candidates(scopes: &[SectionScope]) -> Vec<AutoBoundCandidate> {
    let mut candidates = Vec::new();
    for (depth, scope) in scopes.iter().enumerate() {
        for var in scope.all_variables() {
            candidates.push(AutoBoundCandidate {
                name: var.name.clone(),
                scope_depth: depth,
                is_included: scope.is_included(&var.name),
                is_implicit: var.is_implicit,
            });
        }
    }
    candidates
}

/// Return only auto-bound candidates that are currently included.
#[must_use]
pub(crate) fn active_auto_bound_candidates(scopes: &[SectionScope]) -> Vec<AutoBoundCandidate> {
    analyze_auto_bound_candidates(scopes)
        .into_iter()
        .filter(|c| c.is_included)
        .collect()
}

// ---------------------------------------------------------------------------
// Section dependency analysis
// ---------------------------------------------------------------------------

/// Analyze which variables from outer scopes each scope level depends on.
#[must_use]
pub(crate) fn analyze_section_dependencies(scopes: &[SectionScope]) -> Vec<SectionDependencyInfo> {
    let mut result = Vec::with_capacity(scopes.len());
    for (depth, scope) in scopes.iter().enumerate() {
        let own_variables: Vec<String> = scope
            .all_variables()
            .iter()
            .map(|v| v.name.clone())
            .collect();
        let outer_names: HashSet<String> = scopes
            .iter()
            .take(depth)
            .flat_map(|s| s.all_variables().iter().map(|v| v.name.clone()))
            .collect();
        let mut referenced = HashSet::new();
        for var in scope.all_variables() {
            collect_const_names_from_expr(&var.ty, &mut referenced);
        }
        let mut outer_dependencies: Vec<String> =
            outer_names.intersection(&referenced).cloned().collect();
        outer_dependencies.sort();
        result.push(SectionDependencyInfo {
            scope_depth: depth,
            outer_dependencies,
            own_variables,
        });
    }
    result
}

// ---------------------------------------------------------------------------
// Scope validation
// ---------------------------------------------------------------------------

/// Validate scope consistency: no cross-scope duplicate variables, no
/// universe-variable name collisions.
pub(crate) fn validate_scope_stack(scopes: &[SectionScope]) -> Result<(), ScopeValidationError> {
    let mut seen_vars: HashMap<String, usize> = HashMap::new();
    for (depth, scope) in scopes.iter().enumerate() {
        for var in scope.all_variables() {
            if let Some(&prev_depth) = seen_vars.get(&var.name) {
                if prev_depth != depth {
                    return Err(ScopeValidationError::DuplicateVariable {
                        name: var.name.clone(),
                        depth,
                    });
                }
            }
            seen_vars.insert(var.name.clone(), depth);
        }
        for u in scope.universe_params() {
            if seen_vars.contains_key(u) {
                return Err(ScopeValidationError::UniverseVariableCollision {
                    name: u.clone(),
                    depth,
                });
            }
        }
    }
    Ok(())
}

/// Validate that scope and name slices have matching lengths.
pub(crate) fn validate_scope_nesting(
    scopes: &[SectionScope],
    names: &[&str],
) -> Result<(), ScopeValidationError> {
    if scopes.len() != names.len() {
        return Err(ScopeValidationError::NestingError {
            message: format!(
                "scope count ({}) does not match name count ({})",
                scopes.len(),
                names.len()
            ),
        });
    }
    Ok(())
}
