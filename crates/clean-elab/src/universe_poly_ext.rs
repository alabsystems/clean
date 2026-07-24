// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended universe polymorphism for elaboration.
//!
//! Variable collection, level inference, constraint solving, normalization,
//! cumulative subtyping, metavariable assignment, auto-bound parameters,
//! consistency checking, and level pretty-printing.
//!
//! References: Lean 4 `src/Lean/Level.lean`, `src/Lean/Elab/Level.lean`

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;

use clean_kernel::{Expr, ExprKind, Level, Name};

use crate::stack_safe;

/// Configuration for extended universe polymorphism operations.
#[derive(Debug, Clone)]
pub(crate) struct UniversePolyExtConfig {
    /// Maximum iterations for constraint solving fixed-point.
    pub(crate) max_solve_iterations: usize,
    /// Maximum depth for level normalization recursion.
    pub(crate) max_norm_depth: usize,
    /// Whether to enable cumulative universe subtyping.
    pub(crate) cumulative_enabled: bool,
    /// Prefix for auto-generated universe metavariable names.
    pub(crate) meta_prefix: String,
}

impl Default for UniversePolyExtConfig {
    fn default() -> Self {
        Self {
            max_solve_iterations: 100,
            max_norm_depth: 200,
            cumulative_enabled: true,
            meta_prefix: "_uext".to_owned(),
        }
    }
}

/// Errors from extended universe polymorphism operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum UniversePolyExtError {
    #[error("unsatisfiable universe constraints: {0}")]
    Unsatisfiable(String),
    #[error("cyclic universe constraint: {0}")]
    Cyclic(String),
    #[error("universe normalization depth exceeded (limit: {0})")]
    NormDepthExceeded(usize),
    #[error("unassigned universe metavariable: {0}")]
    UnassignedMeta(String),
}

// ── Universe variable collection ─────────────────────────────────────────

/// Collect all universe parameter names referenced in an expression.
/// Returns names in sorted order for deterministic output.
#[must_use]
pub(crate) fn collect_universe_vars(expr: &Expr) -> Vec<Name> {
    let mut names = BTreeSet::new();
    stack_safe(|| collect_vars_walk(expr, &mut names));
    names.into_iter().collect()
}

fn collect_vars_walk(expr: &Expr, names: &mut BTreeSet<Name>) {
    match expr.kind() {
        ExprKind::Sort(level) => collect_level_params(level, names),
        ExprKind::Const(_, levels) => {
            for l in levels {
                collect_level_params(l, names);
            }
        }
        ExprKind::App(f, a) => {
            stack_safe(|| collect_vars_walk(f, names));
            stack_safe(|| collect_vars_walk(a, names));
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack_safe(|| collect_vars_walk(ty, names));
            stack_safe(|| collect_vars_walk(body, names));
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack_safe(|| collect_vars_walk(ty, names));
            stack_safe(|| collect_vars_walk(val, names));
            stack_safe(|| collect_vars_walk(body, names));
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            stack_safe(|| collect_vars_walk(inner, names));
        }
        _ => {}
    }
}

fn collect_level_params(level: &Level, names: &mut BTreeSet<Name>) {
    match level {
        Level::Zero => {}
        Level::Param(n) => {
            names.insert(n.clone());
        }
        Level::Succ(inner) => collect_level_params(inner, names),
        Level::Max(a, b) | Level::IMax(a, b) => {
            collect_level_params(a, names);
            collect_level_params(b, names);
        }
    }
}

// ── Universe level normalization ─────────────────────────────────────────

/// Normalize a universe level with extended simplification rules.
///
/// Beyond kernel `Level::normalize`: `max(u,u)->u`, `max(0,u)->u`,
/// `imax(a,0)->0`, `max(succ(u),succ(v))->succ(max(u,v))`.
pub(crate) fn normalize_level_ext(level: &Level, config: &UniversePolyExtConfig) -> Level {
    norm_impl(level, config, 0)
}

fn norm_impl(level: &Level, config: &UniversePolyExtConfig, depth: usize) -> Level {
    if depth >= config.max_norm_depth {
        return level.clone();
    }
    match level {
        Level::Zero | Level::Param(_) => level.clone(),
        Level::Succ(inner) => Level::succ(norm_impl(inner, config, depth + 1)),
        Level::Max(a, b) => simplify_max(
            &norm_impl(a, config, depth + 1),
            &norm_impl(b, config, depth + 1),
        ),
        Level::IMax(a, b) => simplify_imax(
            &norm_impl(a, config, depth + 1),
            &norm_impl(b, config, depth + 1),
        ),
    }
}

fn simplify_max(a: &Level, b: &Level) -> Level {
    if a == b {
        return a.clone();
    }
    if a.is_zero() {
        return b.clone();
    }
    if b.is_zero() {
        return a.clone();
    }
    if let (Level::Succ(ia), Level::Succ(ib)) = (a, b) {
        return Level::succ(simplify_max(ia, ib));
    }
    Level::max(a.clone(), b.clone())
}

fn simplify_imax(a: &Level, b: &Level) -> Level {
    if b.is_zero() {
        return Level::zero();
    }
    if matches!(b, Level::Succ(_)) {
        return simplify_max(a, b);
    }
    Level::imax(a.clone(), b.clone())
}

// ── Cumulative universe subtyping ────────────────────────────────────────

/// Check cumulative universe subtyping: `Type u <= Type v` (i.e., `u <= v`).
#[must_use]
pub(crate) fn universe_subtype(u: &Level, v: &Level) -> bool {
    Level::leq(u, v)
}

/// Check strict universe ordering: `Type u < Type v` (i.e., `succ(u) <= v`).
#[must_use]
pub(crate) fn universe_strict_lt(u: &Level, v: &Level) -> bool {
    Level::leq(&Level::succ(u.clone()), v)
}

// ── Universe metavariable assignment ─────────────────────────────────────

/// Context for assigning universe metavariables during elaboration.
#[derive(Debug, Clone)]
pub(crate) struct UniverseMetaCtx {
    config: UniversePolyExtConfig,
    counter: u32,
    assignments: HashMap<Name, Level>,
    constraints: Vec<(Level, Level)>,
}

impl UniverseMetaCtx {
    /// Create with default configuration.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::with_config(UniversePolyExtConfig::default())
    }

    /// Create with custom configuration.
    #[must_use]
    pub(crate) fn with_config(config: UniversePolyExtConfig) -> Self {
        Self {
            config,
            counter: 0,
            assignments: HashMap::new(),
            constraints: Vec::new(),
        }
    }

    /// Generate a fresh universe metavariable level.
    pub(crate) fn fresh_meta(&mut self) -> Level {
        let name = Name::from_string(&format!("{}.{}", self.config.meta_prefix, self.counter));
        self.counter += 1;
        Level::param(name)
    }

    /// Record an equality constraint between two levels.
    pub(crate) fn add_eq_constraint(&mut self, lhs: Level, rhs: Level) {
        self.constraints.push((lhs, rhs));
    }

    /// Assign a concrete level to a universe metavariable.
    pub(crate) fn assign(&mut self, name: &Name, level: Level) -> Result<(), UniversePolyExtError> {
        if level_references(name, &level) {
            return Err(UniversePolyExtError::Cyclic(name.to_string()));
        }
        self.assignments.insert(name.clone(), level);
        Ok(())
    }

    /// Look up the assignment for a name.
    #[must_use]
    pub(crate) fn get_assignment(&self, name: &Name) -> Option<&Level> {
        self.assignments.get(name)
    }

    /// Apply all current assignments to a level.
    pub(crate) fn apply_assignments(&self, level: &Level) -> Level {
        if self.assignments.is_empty() {
            return level.clone();
        }
        let subst: Vec<(Name, Level)> = self
            .assignments
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        level.substitute(&subst)
    }

    /// Solve all accumulated constraints and return the assignment map.
    pub(crate) fn solve(&mut self) -> Result<HashMap<Name, Level>, UniversePolyExtError> {
        let max_iters = self
            .config
            .max_solve_iterations
            .min(self.constraints.len() + 1);
        for _ in 0..max_iters {
            let mut changed = false;
            for i in 0..self.constraints.len() {
                let (lhs, rhs) = self.constraints[i].clone();
                let lhs_sub = self.apply_assignments(&lhs);
                let rhs_sub = self.apply_assignments(&rhs);
                if let Some((name, level)) = try_extract_binding(&lhs_sub, &rhs_sub) {
                    if let std::collections::hash_map::Entry::Vacant(e) =
                        self.assignments.entry(name.clone())
                    {
                        if level_references(&name, &level) {
                            return Err(UniversePolyExtError::Cyclic(name.to_string()));
                        }
                        e.insert(level);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Ok(self.assignments.clone())
    }

    /// Number of current assignments.
    #[must_use]
    pub(crate) fn assignment_count(&self) -> usize {
        self.assignments.len()
    }

    /// Check if a name is a generated metavariable (starts with the prefix).
    #[must_use]
    pub(crate) fn is_meta_name(&self, name: &Name) -> bool {
        name.to_string().starts_with(&self.config.meta_prefix)
    }
}

// ── Auto-bound universe parameters ──────────────────────────────────────

/// Detect free universe variables that should be auto-bound.
///
/// Returns names in the expression that are not in `declared` and do not
/// start with `_` (convention for internal/synthetic names).
#[must_use]
pub(crate) fn auto_bound_universe_params(expr: &Expr, declared: &[Name]) -> Vec<Name> {
    let declared_set: HashSet<&Name> = declared.iter().collect();
    collect_universe_vars(expr)
        .into_iter()
        .filter(|n| !declared_set.contains(n) && !n.to_string().starts_with('_'))
        .collect()
}

// ── Universe consistency checking ────────────────────────────────────────

/// An equality constraint between two universe levels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniverseEqConstraint {
    pub(crate) lhs: Level,
    pub(crate) rhs: Level,
}

impl fmt::Display for UniverseEqConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} = {}",
            pretty_level(&self.lhs),
            pretty_level(&self.rhs)
        )
    }
}

/// Check a set of universe equality constraints for consistency.
pub(crate) fn check_consistency(
    constraints: &[UniverseEqConstraint],
) -> Result<HashMap<Name, Level>, UniversePolyExtError> {
    let mut ctx = UniverseMetaCtx::new();
    for c in constraints {
        ctx.add_eq_constraint(c.lhs.clone(), c.rhs.clone());
    }
    let solution = ctx.solve()?;
    for c in constraints {
        let lhs = substitute_level(&c.lhs, &solution).normalize();
        let rhs = substitute_level(&c.rhs, &solution).normalize();
        if is_ground(&lhs) && is_ground(&rhs) && lhs != rhs {
            return Err(UniversePolyExtError::Unsatisfiable(format!(
                "{} != {}",
                pretty_level(&lhs),
                pretty_level(&rhs)
            )));
        }
    }
    Ok(solution)
}

// ── Universe level inference ─────────────────────────────────────────────

/// Infer the universe level for `(a : A) -> B` where `A : Sort u`, `B : Sort v`.
/// Result is `Sort (imax u v)` per Lean 4 semantics.
pub(crate) fn infer_pi_universe(domain_level: &Level, codomain_level: &Level) -> Level {
    let config = UniversePolyExtConfig::default();
    normalize_level_ext(
        &Level::imax(domain_level.clone(), codomain_level.clone()),
        &config,
    )
}

/// Infer the universe level from multiple usages (pairwise max, normalized).
pub(crate) fn infer_sort_level(usages: &[Level]) -> Level {
    match usages.len() {
        0 => Level::zero(),
        1 => usages[0].normalize(),
        _ => {
            let config = UniversePolyExtConfig::default();
            let mut acc = usages[0].clone();
            for l in &usages[1..] {
                acc = Level::max(acc, l.clone());
            }
            normalize_level_ext(&acc, &config)
        }
    }
}

// ── Universe level pretty-printing ───────────────────────────────────────

/// Render a universe level in human-readable Lean notation.
#[must_use]
pub(crate) fn pretty_level(level: &Level) -> String {
    match level {
        Level::Zero => "0".to_owned(),
        Level::Param(n) => n.to_string(),
        Level::Succ(_) => {
            if let Some(n) = as_numeric(level) {
                return n.to_string();
            }
            let base = base_of_succ(level);
            let offset = succ_offset(level);
            if offset == 1 {
                format!("{} + 1", pretty_level_atom(base))
            } else {
                format!("{} + {offset}", pretty_level_atom(base))
            }
        }
        Level::Max(a, b) => format!("max({}, {})", pretty_level(a), pretty_level(b)),
        Level::IMax(a, b) => format!("imax({}, {})", pretty_level(a), pretty_level(b)),
    }
}

fn pretty_level_atom(level: &Level) -> String {
    match level {
        Level::Zero | Level::Param(_) => pretty_level(level),
        _ => format!("({})", pretty_level(level)),
    }
}

fn as_numeric(level: &Level) -> Option<u64> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(inner) => as_numeric(inner).map(|n| n + 1),
        _ => None,
    }
}

fn succ_offset(level: &Level) -> u64 {
    match level {
        Level::Succ(inner) => 1 + succ_offset(inner),
        _ => 0,
    }
}

fn base_of_succ(level: &Level) -> &Level {
    match level {
        Level::Succ(inner) => base_of_succ(inner),
        _ => level,
    }
}

// ── Internal helpers ─────────────────────────────────────────────────────

fn is_ground(level: &Level) -> bool {
    match level {
        Level::Zero => true,
        Level::Succ(inner) => is_ground(inner),
        Level::Max(a, b) | Level::IMax(a, b) => is_ground(a) && is_ground(b),
        Level::Param(_) => false,
    }
}

fn level_references(name: &Name, level: &Level) -> bool {
    match level {
        Level::Zero => false,
        Level::Param(n) => n == name,
        Level::Succ(inner) => level_references(name, inner),
        Level::Max(a, b) | Level::IMax(a, b) => {
            level_references(name, a) || level_references(name, b)
        }
    }
}

fn try_extract_binding(lhs: &Level, rhs: &Level) -> Option<(Name, Level)> {
    match (lhs, rhs) {
        (Level::Param(name), other) if !matches!(other, Level::Param(n) if n == name) => {
            Some((name.clone(), other.clone()))
        }
        (other, Level::Param(name)) if !matches!(other, Level::Param(n) if n == name) => {
            Some((name.clone(), other.clone()))
        }
        _ => None,
    }
}

fn substitute_level(level: &Level, solutions: &HashMap<Name, Level>) -> Level {
    if solutions.is_empty() {
        return level.clone();
    }
    let subst: Vec<(Name, Level)> = solutions
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    level.substitute(&subst)
}
