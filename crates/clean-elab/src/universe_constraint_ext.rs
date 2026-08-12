// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended universe constraint solving for elaboration.
//!
//! Extends the base `Le`/`Eq` constraints with `Max`/`IMax` result-level
//! relationships. Provides [`ConstraintSet`] for accumulation + solving,
//! [`UniverseSolution`] for applying results, and expression-walking utilities.
//!
//! References: Lean 4 `src/Lean/Level.lean`, `src/Lean/Elab/Level.lean`

use std::collections::HashMap;
use std::fmt;

use clean_kernel::{Expr, ExprKind, Level, Name};

use crate::error::ElabError;
use crate::stack_safe;

/// An extended universe-level constraint with `Max`/`IMax` result tracking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UniverseConstraintExt {
    /// `lhs <= rhs`
    Le(Level, Level),
    /// `lhs == rhs`
    Eq(Level, Level),
    /// `max(a, b) == result`
    Max(Level, Level, Level),
    /// `imax(a, b) == result`
    IMax(Level, Level, Level),
}

impl fmt::Display for UniverseConstraintExt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Le(l, r) => write!(f, "{l} <= {r}"),
            Self::Eq(l, r) => write!(f, "{l} = {r}"),
            Self::Max(a, b, r) => write!(f, "max({a}, {b}) = {r}"),
            Self::IMax(a, b, r) => write!(f, "imax({a}, {b}) = {r}"),
        }
    }
}

/// A fresh universe inference variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct UniverseMetaVar {
    pub(crate) id: usize,
    pub(crate) name: Option<Name>,
}

impl UniverseMetaVar {
    /// Create a new metavariable with the given id and optional name.
    #[must_use]
    pub(crate) fn new(id: usize, name: Option<Name>) -> Self {
        Self { id, name }
    }

    /// Return the `Level::Param` representation of this metavar.
    pub(crate) fn to_level(&self) -> Level {
        let n = self
            .name
            .clone()
            .unwrap_or_else(|| Name::from_string(&format!("_umv.{}", self.id)));
        Level::param(n)
    }
}

impl fmt::Display for UniverseMetaVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.name {
            Some(n) => write!(f, "?{n}"),
            None => write!(f, "?_umv.{}", self.id),
        }
    }
}

/// A mapping from universe parameter names to concrete levels.
#[derive(Debug, Clone, Default)]
pub(crate) struct UniverseSolution {
    map: HashMap<Name, Level>,
}

impl UniverseSolution {
    /// Create an empty solution.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Create from an existing map.
    #[must_use]
    pub(crate) fn from_map(map: HashMap<Name, Level>) -> Self {
        Self { map }
    }

    /// Look up a name.
    #[must_use]
    pub(crate) fn get(&self, name: &Name) -> Option<&Level> {
        self.map.get(name)
    }

    /// Check whether a name is in the solution.
    #[must_use]
    pub(crate) fn contains(&self, name: &Name) -> bool {
        self.map.contains_key(name)
    }

    /// Number of bindings.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the solution is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Iterate over bindings.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Name, &Level)> {
        self.map.iter()
    }

    /// Insert a binding.
    pub(crate) fn insert(&mut self, name: Name, level: Level) {
        self.map.insert(name, level);
    }

    /// Apply this solution to a level, substituting all bound params.
    pub(crate) fn apply_to_level(&self, level: &Level) -> Level {
        if self.map.is_empty() {
            return level.clone();
        }
        let subst: Vec<(Name, Level)> = self
            .map
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        level.substitute(&subst)
    }

    /// Get a reference to the inner map.
    #[must_use]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) fn as_map(&self) -> &HashMap<Name, Level> {
        &self.map
    }
}

/// A mutable set of universe constraints with solving capability.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConstraintSet {
    constraints: Vec<UniverseConstraintExt>,
}

impl ConstraintSet {
    /// Create an empty constraint set.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a constraint.
    pub(crate) fn add_constraint(&mut self, c: UniverseConstraintExt) {
        self.constraints.push(c);
    }

    /// Number of constraints.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Whether the set is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Read-only access to the constraints.
    #[must_use]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) fn constraints(&self) -> &[UniverseConstraintExt] {
        &self.constraints
    }

    /// Check consistency without solving.
    ///
    /// Returns `true` if no immediately contradictory constraints are found.
    /// This is conservative: `true` does not guarantee solvability, but
    /// `false` means there is a definite contradiction.
    #[must_use]
    pub(crate) fn is_consistent(&self) -> bool {
        for c in &self.constraints {
            match c {
                UniverseConstraintExt::Le(lhs, rhs) => {
                    // Both concrete (no params) — can check directly.
                    if is_ground(lhs) && is_ground(rhs) && !Level::leq(lhs, rhs) {
                        return false;
                    }
                }
                UniverseConstraintExt::Eq(lhs, rhs) => {
                    if is_ground(lhs) && is_ground(rhs) && lhs != rhs {
                        return false;
                    }
                }
                UniverseConstraintExt::Max(a, b, r) => {
                    if is_ground(a) && is_ground(b) && is_ground(r) {
                        let expected = Level::max(a.clone(), b.clone()).normalize();
                        let actual = r.normalize();
                        if expected != actual {
                            return false;
                        }
                    }
                }
                UniverseConstraintExt::IMax(a, b, r) => {
                    if is_ground(a) && is_ground(b) && is_ground(r) {
                        let expected = Level::imax(a.clone(), b.clone()).normalize();
                        let actual = r.normalize();
                        if expected != actual {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    /// Remove trivially satisfied constraints in place.
    ///
    /// A constraint is trivial when:
    /// - `Eq(l, l)` — identical sides
    /// - `Le(l, l)` — reflexive
    /// - `Le(Zero, _)` — zero is the least level
    /// - `Max(a, b, r)` / `IMax(a, b, r)` where the result is already `max`/`imax` normal form
    pub(crate) fn simplify(&mut self) {
        self.constraints.retain(|c| match c {
            UniverseConstraintExt::Eq(l, r) => l != r,
            UniverseConstraintExt::Le(l, r) => {
                if l == r {
                    return false;
                }
                if l.is_zero() {
                    return false;
                }
                // If both ground, drop if already satisfied.
                !(is_ground(l) && is_ground(r) && Level::leq(l, r))
            }
            UniverseConstraintExt::Max(a, b, r) => {
                if is_ground(a) && is_ground(b) && is_ground(r) {
                    let expected = Level::max(a.clone(), b.clone()).normalize();
                    let actual = r.normalize();
                    expected != actual
                } else {
                    true
                }
            }
            UniverseConstraintExt::IMax(a, b, r) => {
                if is_ground(a) && is_ground(b) && is_ground(r) {
                    let expected = Level::imax(a.clone(), b.clone()).normalize();
                    let actual = r.normalize();
                    expected != actual
                } else {
                    true
                }
            }
        });
    }

    /// Solve the constraint set, returning a minimal solution.
    ///
    /// Fixed-point iteration: extract `param = level` bindings from `Eq`
    /// constraints and `Max`/`IMax` constraints, substitute, repeat. Then
    /// verify all `Le` constraints.
    pub(crate) fn solve(&self) -> Result<UniverseSolution, ElabError> {
        let mut solution = UniverseSolution::new();
        let max_iters = self.constraints.len() + 1;

        for _ in 0..max_iters {
            let mut changed = false;
            for c in &self.constraints {
                match c {
                    UniverseConstraintExt::Eq(lhs, rhs) => {
                        let ls = solution.apply_to_level(lhs);
                        let rs = solution.apply_to_level(rhs);
                        if let Some((name, level)) = extract_binding(&ls, &rs) {
                            if !solution.contains(&name) {
                                if level_contains_param(&level, &name) {
                                    return Err(ElabError::NotImplemented(format!(
                                        "cyclic universe constraint involving {name}"
                                    )));
                                }
                                solution.insert(name, level);
                                changed = true;
                            }
                        }
                    }
                    UniverseConstraintExt::Max(a, b, r) | UniverseConstraintExt::IMax(a, b, r) => {
                        // If result is a param, bind it to max/imax(a, b).
                        let rs = solution.apply_to_level(r);
                        if let Level::Param(name) = &rs {
                            if !solution.contains(name) {
                                let as_ = solution.apply_to_level(a);
                                let bs = solution.apply_to_level(b);
                                let computed = if matches!(c, UniverseConstraintExt::Max(..)) {
                                    Level::max(as_, bs)
                                } else {
                                    Level::imax(as_, bs)
                                };
                                if level_contains_param(&computed, name) {
                                    return Err(ElabError::NotImplemented(format!(
                                        "cyclic universe constraint involving {name}"
                                    )));
                                }
                                solution.insert(name.clone(), computed);
                                changed = true;
                            }
                        }
                    }
                    UniverseConstraintExt::Le(..) => { /* verified after solving */ }
                }
            }
            if !changed {
                break;
            }
        }

        // Verify Le constraints under the solution.
        for c in &self.constraints {
            if let UniverseConstraintExt::Le(lhs, rhs) = c {
                let ls = solution.apply_to_level(lhs);
                let rs = solution.apply_to_level(rhs);
                if !Level::leq(&ls, &rs) {
                    return Err(ElabError::NotImplemented(format!(
                        "unsolvable universe constraint: {ls} <= {rs}"
                    )));
                }
            }
        }

        Ok(solution)
    }
}

/// Walk an expression collecting universe constraints from `Sort`/`Const` nodes.
/// `Sort(level)` yields `Le(Zero, level)`; multi-level `Const` yields pairwise `Le`.
#[must_use]
pub(crate) fn collect_universe_constraints(expr: &Expr) -> Vec<UniverseConstraintExt> {
    let mut out = Vec::new();
    stack_safe(|| collect_constraints_walk(expr, &mut out));
    out
}

fn collect_constraints_walk(expr: &Expr, out: &mut Vec<UniverseConstraintExt>) {
    match expr.kind() {
        ExprKind::Sort(level) => {
            out.push(UniverseConstraintExt::Le(Level::zero(), level.clone()));
        }
        ExprKind::Const(_, levels) => {
            for pair in levels.windows(2) {
                out.push(UniverseConstraintExt::Le(pair[0].clone(), pair[1].clone()));
            }
        }
        ExprKind::App(f, a) => {
            stack_safe(|| collect_constraints_walk(f, out));
            stack_safe(|| collect_constraints_walk(a, out));
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack_safe(|| collect_constraints_walk(ty, out));
            stack_safe(|| collect_constraints_walk(body, out));
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack_safe(|| collect_constraints_walk(ty, out));
            stack_safe(|| collect_constraints_walk(val, out));
            stack_safe(|| collect_constraints_walk(body, out));
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            stack_safe(|| collect_constraints_walk(inner, out));
        }
        _ => {}
    }
}

/// Check whether a set of constraints is consistent, returning the
/// inconsistent subset on failure.
pub(crate) fn check_universe_consistent(
    constraints: &[UniverseConstraintExt],
) -> Result<(), Vec<UniverseConstraintExt>> {
    let bad: Vec<UniverseConstraintExt> = constraints
        .iter()
        .filter(|c| match c {
            UniverseConstraintExt::Le(l, r) => is_ground(l) && is_ground(r) && !Level::leq(l, r),
            UniverseConstraintExt::Eq(l, r) => is_ground(l) && is_ground(r) && l != r,
            UniverseConstraintExt::Max(a, b, r) => {
                is_ground(a)
                    && is_ground(b)
                    && is_ground(r)
                    && Level::max(a.clone(), b.clone()).normalize() != r.normalize()
            }
            UniverseConstraintExt::IMax(a, b, r) => {
                is_ground(a)
                    && is_ground(b)
                    && is_ground(r)
                    && Level::imax(a.clone(), b.clone()).normalize() != r.normalize()
            }
        })
        .cloned()
        .collect();

    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad)
    }
}

/// From multiple usages of a universe level, infer the most general level.
///
/// Strategy: take the pairwise `max` of all usages, then normalize.
/// An empty input returns `Level::Zero`.
pub(crate) fn infer_universe_level(usages: &[Level]) -> Level {
    match usages.len() {
        0 => Level::zero(),
        1 => usages[0].normalize(),
        _ => {
            let mut acc = usages[0].clone();
            for l in &usages[1..] {
                acc = Level::max(acc, l.clone());
            }
            acc.normalize()
        }
    }
}

/// Apply a solution to a level, substituting all bound parameters.
pub(crate) fn normalize_level(level: &Level, solution: &UniverseSolution) -> Level {
    solution.apply_to_level(level).normalize()
}

/// Check whether `level` transitively references the given metavariable.
///
/// This prevents cyclic bindings in the constraint solver.
#[must_use]
pub(crate) fn occurs_check(var: &UniverseMetaVar, level: &Level) -> bool {
    let target = var
        .name
        .clone()
        .unwrap_or_else(|| Name::from_string(&format!("_umv.{}", var.id)));
    level_contains_param(level, &target)
}

/// Check whether a level is ground (contains no `Param` nodes).
fn is_ground(level: &Level) -> bool {
    match level {
        Level::Zero => true,
        Level::Succ(inner) => is_ground(inner),
        Level::Max(a, b) | Level::IMax(a, b) => is_ground(a) && is_ground(b),
        Level::Param(_) => false,
    }
}

/// Check whether a level references a specific parameter name.
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

/// Try to extract a `param = level` binding from an equality.
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
