// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe polymorphism elaboration support.
//!
//! Handles universe parameter collection, constraint solving, universe inference,
//! and auto-leveling for polymorphic definitions. In Lean 4, definitions can be
//! parametric over universe levels (e.g., `List.{u}`, `Type u`). This module
//! provides the infrastructure to:
//!
//! 1. Collect declared universe parameters from surface declarations
//! 2. Track universe-level constraints during elaboration
//! 3. Solve constraint systems to determine concrete level assignments
//! 4. Automatically insert universe parameters when omitted
//!
//! # Architecture
//!
//! The constraint solver uses a simple worklist algorithm:
//! - `Eq(a, b)` constraints unify levels structurally
//! - `Le(a, b)` constraints are checked via `Level::leq`
//! - Fresh universe metavariables are represented as `Level::Param` with
//!   generated names (e.g., `_u.0`, `_u.1`)
//!
//! # References
//!
//! - Lean 4: `src/Lean/Elab/Level.lean`, `src/Lean/Level.lean`
//! - de Moura & Ullrich, "The Lean 4 Theorem Prover and Programming Language"

mod expr_ops;

use std::collections::HashMap;

use clean_kernel::{Level, Name};
use clean_parser::{LevelExpr, SurfaceDecl, UniverseExpr};

// Re-export expression-level operations for a flat API surface.
#[cfg(test)]
pub(crate) use expr_ops::auto_level_definition;
pub(crate) use expr_ops::collect_level_params_from_expr;
pub(crate) use expr_ops::substitute_levels_in_expr;

/// Errors that can occur during universe polymorphism elaboration.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum UniversePolyError {
    /// A universe constraint could not be solved.
    #[error("unsolvable universe constraint: {0}")]
    Unsolvable(String),

    /// A cyclic dependency was detected among universe variables.
    #[error("cyclic universe constraint involving {0}")]
    CyclicConstraint(String),

    /// An unknown universe parameter was referenced.
    #[error("unknown universe parameter: {0}")]
    UnknownParam(String),
}

/// A universe-level constraint arising during elaboration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UniverseConstraint {
    /// `lhs` must be less than or equal to `rhs`.
    Le(Level, Level),
    /// `lhs` must equal `rhs`.
    Eq(Level, Level),
}

/// Collected universe parameters for a declaration.
#[derive(Debug, Clone)]
pub(crate) struct UniverseParams {
    /// Declared parameter names (in declaration order).
    pub(crate) names: Vec<Name>,
    /// Constraints accumulated during elaboration.
    pub(crate) constraints: Vec<UniverseConstraint>,
}

impl UniverseParams {
    /// Create empty universe parameters.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            names: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Create from a list of parameter name strings.
    #[must_use]
    pub(crate) fn from_names(names: &[String]) -> Self {
        Self {
            names: names.iter().map(|s| Name::from_string(s)).collect(),
            constraints: Vec::new(),
        }
    }
}

/// Universe inference context.
///
/// Tracks fresh universe metavariables, constraints, and solutions during
/// elaboration of a single declaration.
#[derive(Debug)]
pub(crate) struct UniverseInferCtx {
    /// Known universe parameter names (from declaration header).
    params: Vec<Name>,
    /// Counter for generating fresh universe metavariable names.
    fresh_counter: u32,
    /// Accumulated constraints.
    constraints: Vec<UniverseConstraint>,
    /// Solutions for universe metavariables (and params).
    solutions: HashMap<Name, Level>,
}

/// Apply a solutions map to a level using the public `Level::substitute` API.
pub(super) fn apply_subst_to_level(level: &Level, solutions: &HashMap<Name, Level>) -> Level {
    if solutions.is_empty() {
        return level.clone();
    }
    let subst: Vec<(Name, Level)> = solutions
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    level.substitute(&subst)
}

impl UniverseInferCtx {
    /// Create a new inference context with the given declared parameters.
    #[must_use]
    pub(crate) fn new(params: Vec<Name>) -> Self {
        Self {
            params,
            fresh_counter: 0,
            constraints: Vec::new(),
            solutions: HashMap::new(),
        }
    }

    /// Generate a fresh universe metavariable.
    ///
    /// Returns a `Level::Param` with a synthetic name like `_u.0`.
    pub(crate) fn fresh_universe(&mut self) -> Level {
        let name = Name::from_string(&format!("_u.{}", self.fresh_counter));
        self.fresh_counter += 1;
        Level::param(name)
    }

    /// Record a universe constraint.
    pub(crate) fn add_constraint(&mut self, constraint: UniverseConstraint) {
        self.constraints.push(constraint);
    }

    /// Record an equality constraint.
    pub(crate) fn add_eq(&mut self, lhs: Level, rhs: Level) {
        self.constraints.push(UniverseConstraint::Eq(lhs, rhs));
    }

    /// Record a less-than-or-equal constraint.
    pub(crate) fn add_le(&mut self, lhs: Level, rhs: Level) {
        self.constraints.push(UniverseConstraint::Le(lhs, rhs));
    }

    /// Get the current constraints.
    #[must_use]
    pub(crate) fn constraints(&self) -> &[UniverseConstraint] {
        &self.constraints
    }

    /// Get the declared parameter names.
    #[must_use]
    pub(crate) fn params(&self) -> &[Name] {
        &self.params
    }

    /// Get the current solutions map.
    #[must_use]
    pub(crate) fn solutions(&self) -> &HashMap<Name, Level> {
        &self.solutions
    }

    /// Solve all accumulated constraints.
    ///
    /// Uses a fixed-point iteration: for each `Eq(a, b)` constraint, attempts
    /// to extract a binding `param -> level`. Iterates until no new bindings
    /// are discovered. Le constraints are verified after Eq constraints are
    /// resolved.
    pub(crate) fn solve(&mut self) -> Result<HashMap<Name, Level>, UniversePolyError> {
        let max_iterations = self.constraints.len() + 1;
        for _ in 0..max_iterations {
            let mut changed = false;
            for i in 0..self.constraints.len() {
                let constraint = self.constraints[i].clone();
                if let UniverseConstraint::Eq(ref lhs, ref rhs) = constraint {
                    let lhs_sub = apply_subst_to_level(lhs, &self.solutions);
                    let rhs_sub = apply_subst_to_level(rhs, &self.solutions);
                    if let Some((name, level)) = extract_binding(&lhs_sub, &rhs_sub) {
                        if let std::collections::hash_map::Entry::Vacant(e) =
                            self.solutions.entry(name.clone())
                        {
                            if level_contains_param(&level, &name) {
                                return Err(UniversePolyError::CyclicConstraint(name.to_string()));
                            }
                            e.insert(level);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Verify Le constraints using the public Level::leq API.
        for constraint in &self.constraints {
            if let UniverseConstraint::Le(lhs, rhs) = constraint {
                let lhs_sub = apply_subst_to_level(lhs, &self.solutions);
                let rhs_sub = apply_subst_to_level(rhs, &self.solutions);
                if !Level::leq(&lhs_sub, &rhs_sub) {
                    return Err(UniversePolyError::Unsolvable(format!(
                        "{lhs_sub} <= {rhs_sub}"
                    )));
                }
            }
        }

        Ok(self.solutions.clone())
    }

    /// Apply the current solution map to a level.
    pub(crate) fn apply_solutions_to_level(&self, level: &Level) -> Level {
        apply_subst_to_level(level, &self.solutions)
    }

    /// Apply the solution map to all universe levels in an expression.
    pub(crate) fn apply_solution(&self, expr: &clean_kernel::Expr) -> clean_kernel::Expr {
        if self.solutions.is_empty() {
            return expr.clone();
        }
        substitute_levels_in_expr(expr, &self.solutions)
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Level-only helper functions
// ═══════════════════════════════════════════════════════════════════════════

/// Try to extract a `param = level` binding from an equality of levels.
fn extract_binding(lhs: &Level, rhs: &Level) -> Option<(Name, Level)> {
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

/// Check whether a level expression references a given parameter name.
fn level_contains_param(level: &Level, name: &Name) -> bool {
    match level {
        Level::Zero => false,
        Level::Param(n) => n == name,
        Level::Succ(inner) => level_contains_param(inner, name),
        Level::Max(a, b) | Level::IMax(a, b) => {
            level_contains_param(a, name) || level_contains_param(b, name)
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Surface syntax conversion functions
// ═══════════════════════════════════════════════════════════════════════════

/// Collect universe parameters from a surface declaration.
#[must_use]
pub(crate) fn collect_universe_params(decl: &SurfaceDecl) -> UniverseParams {
    let names: &[String] = match decl {
        SurfaceDecl::Def {
            universe_params, ..
        }
        | SurfaceDecl::Theorem {
            universe_params, ..
        }
        | SurfaceDecl::Axiom {
            universe_params, ..
        }
        | SurfaceDecl::Opaque {
            universe_params, ..
        }
        | SurfaceDecl::Inductive {
            universe_params, ..
        } => universe_params,
        _ => return UniverseParams::new(),
    };
    UniverseParams::from_names(names)
}

/// Convert a surface `LevelExpr` to a kernel `Level`.
pub(crate) fn level_expr_to_level(expr: &LevelExpr) -> Level {
    match expr {
        LevelExpr::Lit(n) => {
            let mut level = Level::zero();
            for _ in 0..*n {
                level = Level::succ(level);
            }
            level
        }
        LevelExpr::Param(name) => Level::param(Name::from_string(name)),
        LevelExpr::Succ(inner) => Level::succ(level_expr_to_level(inner)),
        LevelExpr::Max(a, b) => Level::max(level_expr_to_level(a), level_expr_to_level(b)),
        LevelExpr::IMax(a, b) => Level::imax(level_expr_to_level(a), level_expr_to_level(b)),
        LevelExpr::Antiquot(name) => Level::param(Name::from_string(name)),
    }
}

/// Convert a surface `UniverseExpr` to a kernel `Level`.
pub(crate) fn universe_expr_to_level(expr: &UniverseExpr, ctx: &mut UniverseInferCtx) -> Level {
    match expr {
        UniverseExpr::Prop => Level::zero(),
        UniverseExpr::Type => Level::succ(Level::zero()),
        UniverseExpr::TypeLevel(level_expr) => Level::succ(level_expr_to_level(level_expr)),
        UniverseExpr::TypeImplicit => Level::succ(ctx.fresh_universe()),
        UniverseExpr::Sort(level_expr) => level_expr_to_level(level_expr),
        UniverseExpr::SortImplicit | UniverseExpr::SortStar => ctx.fresh_universe(),
    }
}
