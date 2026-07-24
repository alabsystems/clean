// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended auto-bound implicit variable elaboration.
//!
//! This module extends the surface-level auto-bound detection in [`super::auto_bound`]
//! with kernel-level operations: walking kernel `Expr` trees to find free variables,
//! inferring binder types from usage context, topologically sorting auto-bound
//! variables by dependency, detecting cycles, and abstracting expressions under
//! auto-bound Pi/Lambda binders.
//!
//! The surface-level module discovers candidates from parsed syntax; this module
//! works on elaborated kernel expressions to produce the final implicit binders.
//!
//! Reference: Lean 4 `src/Lean/Elab/Term.lean` (auto-bound logic),
//! `src/Lean/Elab/PreDefinition/Basic.lean`.

use std::collections::{HashMap, HashSet, VecDeque};

use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::error::ElabError;

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for auto-bound implicit variable elaboration.
#[derive(Debug, Clone)]
pub(crate) struct AutoBoundConfig {
    /// Maximum nesting depth for expression traversal (default: 8).
    pub max_depth: usize,
    /// Whether to auto-bind sort (universe) variables (default: true).
    pub allow_sort_vars: bool,
    /// Whether to emit warnings on ambiguous type inference (default: false).
    pub warn_on_ambiguity: bool,
}

impl Default for AutoBoundConfig {
    fn default() -> Self {
        Self {
            max_depth: 8,
            allow_sort_vars: true,
            warn_on_ambiguity: false,
        }
    }
}

// =============================================================================
// AutoBoundEntry
// =============================================================================

/// A single auto-bound variable entry with its inferred type and binder metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AutoBoundEntry {
    /// The variable name.
    pub name: Name,
    /// The inferred type expression for this variable.
    pub type_expr: Expr,
    /// How the variable should be bound (Implicit, InstImplicit, etc.).
    pub binder_info: BinderInfo,
    /// Optional source span (start, end) for diagnostics.
    pub source_span: Option<(usize, usize)>,
}

// =============================================================================
// AutoBoundContext (scope stack)
// =============================================================================

/// Context maintaining a stack of auto-bound variable scopes.
///
/// Supports nested definitions: each `enter_scope()`/`leave_scope()` pair
/// isolates auto-bound variables discovered within that scope.
pub(crate) struct AutoBoundContext {
    /// Stack of scopes; each scope collects its own auto-bound entries.
    scopes: Vec<Vec<AutoBoundEntry>>,
    /// Configuration controlling traversal depth, sort vars, etc.
    config: AutoBoundConfig,
}

impl AutoBoundContext {
    /// Create a new context with default configuration.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            scopes: vec![Vec::new()],
            config: AutoBoundConfig::default(),
        }
    }

    /// Create a new context with the given configuration.
    #[must_use]
    pub(crate) fn with_config(config: AutoBoundConfig) -> Self {
        Self {
            scopes: vec![Vec::new()],
            config,
        }
    }

    /// Enter a new nested scope for auto-bound variable collection.
    pub(crate) fn enter_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Leave the current scope, returning its collected auto-bound entries.
    ///
    /// Returns an empty Vec if only the root scope remains (root is never popped).
    pub(crate) fn leave_scope(&mut self) -> Vec<AutoBoundEntry> {
        if self.scopes.len() > 1 {
            self.scopes.pop().unwrap_or_default()
        } else {
            Vec::new()
        }
    }

    /// Register a free variable in the current scope.
    ///
    /// If `expected_type` is provided, it is used directly; otherwise the type
    /// defaults to `Type` (Sort 1).
    pub(crate) fn register_free_variable(&mut self, name: &Name, expected_type: Option<&Expr>) {
        let type_expr = expected_type.cloned().unwrap_or_else(Expr::type_);
        let entry = AutoBoundEntry {
            name: name.clone(),
            type_expr,
            binder_info: BinderInfo::Implicit,
            source_span: None,
        };
        if let Some(scope) = self.scopes.last_mut() {
            // Deduplicate by name within the scope.
            if !scope.iter().any(|e| e.name == entry.name) {
                scope.push(entry);
            }
        }
    }

    /// Get the auto-bound entries in the current (innermost) scope.
    #[must_use]
    pub(crate) fn get_auto_bounds(&self) -> &[AutoBoundEntry] {
        self.scopes.last().map_or(&[], |s| s.as_slice())
    }

    /// Get a reference to the configuration.
    #[must_use]
    pub(crate) fn config(&self) -> &AutoBoundConfig {
        &self.config
    }

    /// Return the current scope depth (number of active scopes).
    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.scopes.len()
    }
}

// =============================================================================
// Free variable collection from kernel Expr
// =============================================================================

/// Walk a kernel `Expr` and collect all `FVar` and unresolved `Const` names
/// that are not in the `declared` set.
///
/// This operates on elaborated kernel expressions (not surface syntax).
/// Returns names in first-occurrence order.
#[must_use]
pub(crate) fn collect_free_variables(expr: &Expr, declared: &[Name]) -> Vec<Name> {
    let declared_set: HashSet<&Name> = declared.iter().collect();
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    collect_free_vars_inner(expr, &declared_set, &mut found, &mut seen, 0, 64);
    found
}

fn collect_free_vars_inner(
    expr: &Expr,
    declared: &HashSet<&Name>,
    found: &mut Vec<Name>,
    seen: &mut HashSet<Name>,
    depth: usize,
    max_depth: usize,
) {
    if depth >= max_depth {
        return;
    }
    match expr.kind() {
        ExprKind::FVar(_id) => {
            // FVars don't carry a Name directly in ExprKind; they are
            // resolved via the local context. We skip them here since
            // auto-bound detection at the kernel level primarily targets
            // Const references that are unresolved.
        }
        ExprKind::Const(name, _levels) if !declared.contains(name) && !seen.contains(name) => {
            seen.insert(name.clone());
            found.push(name.clone());
        }
        ExprKind::App(func, arg) => {
            collect_free_vars_inner(func, declared, found, seen, depth + 1, max_depth);
            collect_free_vars_inner(arg, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::Lam(_bd, ty, body) | ExprKind::Pi(_bd, ty, body) => {
            collect_free_vars_inner(ty, declared, found, seen, depth + 1, max_depth);
            collect_free_vars_inner(body, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::Let(_name, ty, val, body, _non_dep) => {
            collect_free_vars_inner(ty, declared, found, seen, depth + 1, max_depth);
            collect_free_vars_inner(val, declared, found, seen, depth + 1, max_depth);
            collect_free_vars_inner(body, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::Proj(_struct_name, _idx, inner) => {
            collect_free_vars_inner(inner, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::MData(_meta, inner) => {
            collect_free_vars_inner(inner, declared, found, seen, depth + 1, max_depth);
        }
        // BVar, Sort, Lit, and extension nodes carry no free names to collect.
        _ => {}
    }
}

// =============================================================================
// Binder type inference
// =============================================================================

/// Infer the binder type for an auto-bound variable from its usage contexts.
///
/// Heuristics:
/// - If any usage is inside a `Sort`, the variable is a universe-level type: `Type`.
/// - If any usage is in a position expecting `Prop`, return `Prop`.
/// - Otherwise, default to `Type` (Sort 1).
pub(crate) fn infer_binder_type(_name: &Name, usages: &[&Expr]) -> Expr {
    for usage in usages {
        match usage.kind() {
            ExprKind::Sort(level) if level == &Level::zero() => {
                return Expr::prop();
            }
            _ => {}
        }
    }
    // Default: bind as Type
    Expr::type_()
}

// =============================================================================
// Dependency sorting
// =============================================================================

/// Topologically sort auto-bound entries so that if variable B appears in
/// the type of variable A, then B is bound before A (i.e., B appears earlier
/// in the output).
///
/// This ensures that when we wrap with Pi binders (outermost first), types
/// are well-scoped.
pub(crate) fn sort_by_dependency(bounds: &mut Vec<AutoBoundEntry>) {
    if bounds.len() <= 1 {
        return;
    }

    // Build name-to-index map.
    let name_to_idx: HashMap<&Name, usize> = bounds
        .iter()
        .enumerate()
        .map(|(i, e)| (&e.name, i))
        .collect();

    let n = bounds.len();
    // adjacency: deps[i] = set of indices that i depends on (appear in i's type).
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, entry) in bounds.iter().enumerate() {
        let free = collect_free_variables(&entry.type_expr, &[]);
        for free_name in &free {
            if let Some(&j) = name_to_idx.get(free_name) {
                if j != i {
                    deps[i].insert(j);
                }
            }
        }
    }

    // Kahn's algorithm for topological sort. If deps[i] contains j, then
    // i depends on j, so j must come first.
    let mut in_deg = vec![0usize; n];
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, d) in deps.iter().enumerate() {
        in_deg[i] = d.len();
        for &j in d {
            dependents[j].push(i);
        }
    }

    let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_deg[i] == 0).collect();
    let mut order = Vec::with_capacity(n);

    while let Some(node) = queue.pop_front() {
        order.push(node);
        for &dep in &dependents[node] {
            in_deg[dep] -= 1;
            if in_deg[dep] == 0 {
                queue.push_back(dep);
            }
        }
    }

    // If order.len() < n, there's a cycle; leave original order (cycle detection
    // is handled by check_no_cycles).
    if order.len() == n {
        let old = std::mem::take(bounds);
        *bounds = order.into_iter().map(|i| old[i].clone()).collect();
    }
}

// =============================================================================
// Cycle detection
// =============================================================================

/// Check that no cyclic dependencies exist among auto-bound variable types.
///
/// Returns `Err(ElabError)` if a cycle is found.
pub(crate) fn check_no_cycles(bounds: &[AutoBoundEntry]) -> Result<(), ElabError> {
    if bounds.len() <= 1 {
        return Ok(());
    }

    let name_to_idx: HashMap<&Name, usize> = bounds
        .iter()
        .enumerate()
        .map(|(i, e)| (&e.name, i))
        .collect();

    let n = bounds.len();
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, entry) in bounds.iter().enumerate() {
        let free = collect_free_variables(&entry.type_expr, &[]);
        for free_name in &free {
            if let Some(&j) = name_to_idx.get(free_name) {
                if j != i {
                    deps[i].insert(j);
                }
            }
        }
    }

    // DFS-based cycle detection.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color = vec![Color::White; n];

    fn dfs(node: usize, deps: &[HashSet<usize>], color: &mut [Color]) -> bool {
        color[node] = Color::Gray;
        for &dep in &deps[node] {
            match color[dep] {
                Color::Gray => return true, // cycle
                Color::White => {
                    if dfs(dep, deps, color) {
                        return true;
                    }
                }
                Color::Black => {}
            }
        }
        color[node] = Color::Black;
        false
    }

    for i in 0..n {
        if color[i] == Color::White && dfs(i, &deps, &mut color) {
            return Err(ElabError::NotImplemented(
                "cyclic dependency among auto-bound implicit variables".to_owned(),
            ));
        }
    }

    Ok(())
}

// =============================================================================
// Abstraction: wrap expression with binders
// =============================================================================

/// Wrap an expression with Pi binders for all auto-bound entries.
///
/// The entries should be pre-sorted by dependency (via `sort_by_dependency`).
/// The first entry becomes the outermost binder.
///
/// For Pi types (signatures): wraps with `Pi {name : type} body`.
/// Uses de Bruijn indexing; the body's existing BVar indices are not shifted
/// since auto-bound variables are prepended at the outermost level and the
/// body is expected to reference them by name resolution, not BVar index.
pub(crate) fn abstract_auto_bounds_pi(expr: Expr, bounds: &[AutoBoundEntry]) -> Expr {
    let mut result = expr;
    for entry in bounds.iter().rev() {
        result = Expr::pi(entry.binder_info, entry.type_expr.clone(), result);
    }
    result
}

/// Wrap an expression with Lambda binders for all auto-bound entries.
///
/// Like `abstract_auto_bounds_pi` but uses Lambda instead of Pi,
/// suitable for wrapping definition bodies.
pub(crate) fn abstract_auto_bounds_lam(expr: Expr, bounds: &[AutoBoundEntry]) -> Expr {
    let mut result = expr;
    for entry in bounds.iter().rev() {
        result = Expr::lam(entry.binder_info, entry.type_expr.clone(), result);
    }
    result
}
