// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended universe polymorphism analysis (phase 2).
//!
//! Constraint solving with explanations, level estimation, conflict detection,
//! statistics, auto-annotation suggestions, monomorphization, visualization.
//!
//! References: Lean 4 `src/Lean/Level.lean`, `src/Lean/Elab/Level.lean`

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use clean_kernel::{Level, Name};

use crate::universe_poly::{UniverseConstraint, UniverseParams};
use crate::universe_poly_ext::{normalize_level_ext, pretty_level, UniversePolyExtConfig};

/// Errors from extended universe polymorphism analysis.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum UniverseExt2Error {
    #[error("conflicting constraints: {explanation}")]
    ConflictingConstraints { explanation: String },
    #[error("no valid level assignment for parameter {param}")]
    NoValidAssignment { param: String },
    #[error("constraint system too large: {count} constraints (limit: {limit})")]
    TooManyConstraints { count: usize, limit: usize },
}

// ── Constraint conflict detection ───────────────────────────────────────

/// A diagnosed conflict between two universe constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstraintConflict {
    pub(crate) lhs: UniverseConstraint,
    pub(crate) rhs: UniverseConstraint,
    pub(crate) explanation: String,
}

impl fmt::Display for ConstraintConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "conflict: {}", self.explanation)
    }
}

/// Detect conflicting constraints within a constraint set.
#[must_use]
pub(crate) fn detect_conflicts(constraints: &[UniverseConstraint]) -> Vec<ConstraintConflict> {
    let bindings = build_eq_bindings(constraints);
    let mut out = detect_eq_eq_conflicts(constraints, &bindings);
    out.extend(detect_eq_le_conflicts(constraints, &bindings));
    out
}

type EqBindings = HashMap<String, Vec<(Level, usize)>>;

fn build_eq_bindings(constraints: &[UniverseConstraint]) -> EqBindings {
    let mut b: EqBindings = HashMap::new();
    for (idx, c) in constraints.iter().enumerate() {
        if let UniverseConstraint::Eq(lhs, rhs) = c {
            if let Level::Param(n) = lhs {
                b.entry(n.to_string()).or_default().push((rhs.clone(), idx));
            }
            if let Level::Param(n) = rhs {
                b.entry(n.to_string()).or_default().push((lhs.clone(), idx));
            }
        }
    }
    b
}

fn detect_eq_eq_conflicts(cs: &[UniverseConstraint], eb: &EqBindings) -> Vec<ConstraintConflict> {
    let mut out = Vec::new();
    for (param, bindings) in eb {
        let ground: Vec<_> = bindings.iter().filter(|(l, _)| is_ground(l)).collect();
        for i in 0..ground.len() {
            for j in (i + 1)..ground.len() {
                let (na, nb) = (ground[i].0.normalize(), ground[j].0.normalize());
                if na != nb {
                    out.push(ConstraintConflict {
                        lhs: cs[ground[i].1].clone(),
                        rhs: cs[ground[j].1].clone(),
                        explanation: format!(
                            "{param} is constrained to both {} and {}",
                            pretty_level(&na),
                            pretty_level(&nb),
                        ),
                    });
                }
            }
        }
    }
    out
}

fn detect_eq_le_conflicts(cs: &[UniverseConstraint], eb: &EqBindings) -> Vec<ConstraintConflict> {
    let mut out = Vec::new();
    for (param, bindings) in eb {
        for (eq_level, eq_idx) in bindings {
            if !is_ground(eq_level) {
                continue;
            }
            let en = eq_level.normalize();
            for (li, c) in cs.iter().enumerate() {
                if let UniverseConstraint::Le(lhs, rhs) = c {
                    if let Level::Param(n) = lhs {
                        if n.to_string() == *param
                            && is_ground(rhs)
                            && !Level::leq(&en, &rhs.normalize())
                        {
                            out.push(ConstraintConflict {
                                lhs: cs[*eq_idx].clone(),
                                rhs: c.clone(),
                                explanation: format!(
                                    "{param} = {} but also {param} <= {}",
                                    pretty_level(&en),
                                    pretty_level(&rhs.normalize()),
                                ),
                            });
                        }
                    }
                    if let Level::Param(n) = rhs {
                        if n.to_string() == *param
                            && is_ground(lhs)
                            && !Level::leq(&lhs.normalize(), &en)
                        {
                            out.push(ConstraintConflict {
                                lhs: cs[*eq_idx].clone(),
                                rhs: cs[li].clone(),
                                explanation: format!(
                                    "{param} = {} but {} <= {param} is required",
                                    pretty_level(&en),
                                    pretty_level(&lhs.normalize()),
                                ),
                            });
                        }
                    }
                }
            }
        }
    }
    out
}

// ── Universe level estimation ───────────────────────────────────────────

/// Estimated universe level assignment with confidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LevelEstimate {
    pub(crate) param: Name,
    pub(crate) level: Level,
    pub(crate) source: EstimateSource,
}

/// How a level estimate was derived.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EstimateSource {
    DirectEquality,
    LowerBound,
    Default,
}

/// Estimate minimal universe levels for parameters from a constraint set.
#[must_use]
pub(crate) fn estimate_levels(constraints: &[UniverseConstraint]) -> Vec<LevelEstimate> {
    collect_params(constraints)
        .into_iter()
        .map(|p| estimate_one(&p, constraints))
        .collect()
}

fn estimate_one(param: &Name, constraints: &[UniverseConstraint]) -> LevelEstimate {
    if let Some(level) = find_ground_eq(param, constraints) {
        return LevelEstimate {
            param: param.clone(),
            level,
            source: EstimateSource::DirectEquality,
        };
    }
    let ps = param.to_string();
    let bounds: Vec<Level> = constraints
        .iter()
        .filter_map(|c| {
            if let UniverseConstraint::Le(lhs, Level::Param(n)) = c {
                if n.to_string() == ps && is_ground(lhs) {
                    return Some(lhs.normalize());
                }
            }
            None
        })
        .collect();
    if let Some(max_b) = bounds
        .into_iter()
        .reduce(|a, l| normalize_level_ext(&Level::max(a, l), &UniversePolyExtConfig::default()))
    {
        LevelEstimate {
            param: param.clone(),
            level: max_b,
            source: EstimateSource::LowerBound,
        }
    } else {
        LevelEstimate {
            param: param.clone(),
            level: Level::zero(),
            source: EstimateSource::Default,
        }
    }
}

// ── Universe statistics ─────────────────────────────────────────────────

/// Statistics about a universe constraint system.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniverseStats {
    pub(crate) param_count: usize,
    pub(crate) eq_count: usize,
    pub(crate) le_count: usize,
    pub(crate) max_ground_level: u64,
    pub(crate) polymorphism_degree: usize,
}

impl fmt::Display for UniverseStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "params={}, eq={}, le={}, max_level={}, poly_degree={}",
            self.param_count,
            self.eq_count,
            self.le_count,
            self.max_ground_level,
            self.polymorphism_degree
        )
    }
}

/// Compute statistics for a universe constraint system.
#[must_use]
pub(crate) fn compute_stats(params: &UniverseParams) -> UniverseStats {
    let all_params = collect_params(&params.constraints);
    let (mut eq_c, mut le_c, mut max_g) = (0usize, 0usize, 0u64);
    for c in &params.constraints {
        match c {
            UniverseConstraint::Eq(l, r) => {
                eq_c += 1;
                max_g = max_g.max(gdepth(l)).max(gdepth(r));
            }
            UniverseConstraint::Le(l, r) => {
                le_c += 1;
                max_g = max_g.max(gdepth(l)).max(gdepth(r));
            }
        }
    }
    let bound: HashSet<String> = params
        .constraints
        .iter()
        .filter_map(ground_eq_param_name)
        .collect();
    let poly = all_params
        .iter()
        .filter(|p| !bound.contains(&p.to_string()))
        .count();
    UniverseStats {
        param_count: all_params.len(),
        eq_count: eq_c,
        le_count: le_c,
        max_ground_level: max_g,
        polymorphism_degree: poly,
    }
}

fn ground_eq_param_name(c: &UniverseConstraint) -> Option<String> {
    if let UniverseConstraint::Eq(lhs, rhs) = c {
        if let Level::Param(n) = lhs {
            if is_ground(rhs) {
                return Some(n.to_string());
            }
        }
        if let Level::Param(n) = rhs {
            if is_ground(lhs) {
                return Some(n.to_string());
            }
        }
    }
    None
}

// ── Auto-universe inference ─────────────────────────────────────────────

/// A suggestion for a universe annotation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniverseSuggestion {
    pub(crate) param: Name,
    pub(crate) suggested_level: Level,
    pub(crate) reason: String,
}

/// Suggest universe level annotations for unresolved parameters.
#[must_use]
pub(crate) fn suggest_annotations(params: &UniverseParams) -> Vec<UniverseSuggestion> {
    estimate_levels(&params.constraints)
        .into_iter()
        .filter(|e| e.source != EstimateSource::DirectEquality)
        .map(|e| {
            let reason = match e.source {
                EstimateSource::LowerBound => {
                    format!("lower bound {} from Le constraints", pretty_level(&e.level))
                }
                EstimateSource::Default => "no constraints; defaulting to 0".to_owned(),
                EstimateSource::DirectEquality => unreachable!(),
            };
            UniverseSuggestion {
                param: e.param,
                suggested_level: e.level,
                reason,
            }
        })
        .collect()
}

// ── Universe monomorphization ───────────────────────────────────────────

/// Result of monomorphization analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MonomorphResult {
    pub(crate) can_monomorphize: bool,
    pub(crate) assignments: BTreeMap<String, Level>,
    pub(crate) remaining_poly: Vec<Name>,
}

/// Analyze whether universe polymorphism can be monomorphized.
#[must_use]
pub(crate) fn analyze_monomorphization(params: &UniverseParams) -> MonomorphResult {
    let all = collect_params(&params.constraints);
    let mut assignments = BTreeMap::new();
    let mut remaining = Vec::new();
    for p in &all {
        if let Some(level) = find_ground_eq(p, &params.constraints) {
            assignments.insert(p.to_string(), level);
        } else {
            remaining.push(p.clone());
        }
    }
    MonomorphResult {
        can_monomorphize: remaining.is_empty() && !all.is_empty(),
        assignments,
        remaining_poly: remaining,
    }
}

// ── Constraint visualization ────────────────────────────────────────────

/// Format a constraint system as a human-readable multi-line string.
#[must_use]
pub(crate) fn format_constraints(constraints: &[UniverseConstraint]) -> String {
    if constraints.is_empty() {
        return "(no constraints)".to_owned();
    }
    constraints
        .iter()
        .enumerate()
        .map(|(i, c)| match c {
            UniverseConstraint::Eq(l, r) => {
                format!("  [{}] {} = {}", i + 1, pretty_level(l), pretty_level(r))
            }
            UniverseConstraint::Le(l, r) => {
                format!("  [{}] {} <= {}", i + 1, pretty_level(l), pretty_level(r))
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Format a constraint system with a summary header.
#[must_use]
pub(crate) fn format_constraint_system(params: &UniverseParams) -> String {
    let s = compute_stats(params);
    format!(
        "Universe constraint system ({} params, {} constraints):\n{}",
        s.param_count,
        s.eq_count + s.le_count,
        format_constraints(&params.constraints)
    )
}

// ── Constraint solving with explanations ────────────────────────────────

/// Result of solving a constraint system with explanations.
#[derive(Debug, Clone)]
pub(crate) struct SolveResult {
    pub(crate) solutions: HashMap<Name, Level>,
    pub(crate) unsolved: Vec<Name>,
    pub(crate) conflicts: Vec<ConstraintConflict>,
}

const MAX_CONSTRAINTS: usize = 10_000;

/// Solve a constraint system with conflict detection and explanations.
pub(crate) fn solve_with_explanations(
    constraints: &[UniverseConstraint],
) -> Result<SolveResult, UniverseExt2Error> {
    if constraints.len() > MAX_CONSTRAINTS {
        return Err(UniverseExt2Error::TooManyConstraints {
            count: constraints.len(),
            limit: MAX_CONSTRAINTS,
        });
    }
    let conflicts = detect_conflicts(constraints);
    if !conflicts.is_empty() {
        return Ok(SolveResult {
            solutions: HashMap::new(),
            unsolved: collect_params(constraints),
            conflicts,
        });
    }
    let all = collect_params(constraints);
    let mut solutions: HashMap<Name, Level> = HashMap::new();
    for _ in 0..constraints.len() + 1 {
        let mut changed = false;
        for c in constraints {
            if let UniverseConstraint::Eq(lhs, rhs) = c {
                let (ls, rs) = (apply_sol(lhs, &solutions), apply_sol(rhs, &solutions));
                if let Some((n, l)) = try_extract(&ls, &rs) {
                    if !solutions.contains_key(&n) && !level_refs(&l, &n) {
                        solutions.insert(n, l);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let unsolved = all
        .into_iter()
        .filter(|p| !solutions.contains_key(p))
        .collect();
    Ok(SolveResult {
        solutions,
        unsolved,
        conflicts: Vec::new(),
    })
}

// ── Internal helpers ────────────────────────────────────────────────────

fn is_ground(level: &Level) -> bool {
    match level {
        Level::Zero => true,
        Level::Succ(inner) => is_ground(inner),
        Level::Max(a, b) | Level::IMax(a, b) => is_ground(a) && is_ground(b),
        Level::Param(_) => false,
    }
}

fn gdepth(level: &Level) -> u64 {
    match level {
        Level::Zero => 0,
        Level::Succ(inner) if is_ground(level) => 1 + gdepth(inner),
        Level::Max(a, b) if is_ground(level) => gdepth(a).max(gdepth(b)),
        Level::IMax(_, b) if is_ground(level) => {
            if b.is_zero() {
                0
            } else {
                gdepth(b)
            }
        }
        _ => 0,
    }
}

/// Find a ground equality binding for a parameter in a constraint set.
fn find_ground_eq(param: &Name, constraints: &[UniverseConstraint]) -> Option<Level> {
    let ps = param.to_string();
    constraints.iter().find_map(|c| {
        if let UniverseConstraint::Eq(lhs, rhs) = c {
            if let Level::Param(n) = lhs {
                if n.to_string() == ps && is_ground(rhs) {
                    return Some(rhs.normalize());
                }
            }
            if let Level::Param(n) = rhs {
                if n.to_string() == ps && is_ground(lhs) {
                    return Some(lhs.normalize());
                }
            }
        }
        None
    })
}

fn collect_params(constraints: &[UniverseConstraint]) -> Vec<Name> {
    let mut names = BTreeSet::new();
    for c in constraints {
        match c {
            UniverseConstraint::Eq(l, r) | UniverseConstraint::Le(l, r) => {
                collect_lvl_names(l, &mut names);
                collect_lvl_names(r, &mut names);
            }
        }
    }
    names.into_iter().collect()
}

fn collect_lvl_names(level: &Level, names: &mut BTreeSet<Name>) {
    match level {
        Level::Zero => {}
        Level::Param(n) => {
            names.insert(n.clone());
        }
        Level::Succ(inner) => collect_lvl_names(inner, names),
        Level::Max(a, b) | Level::IMax(a, b) => {
            collect_lvl_names(a, names);
            collect_lvl_names(b, names);
        }
    }
}

fn apply_sol(level: &Level, sol: &HashMap<Name, Level>) -> Level {
    if sol.is_empty() {
        return level.clone();
    }
    let s: Vec<(Name, Level)> = sol.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    level.substitute(&s)
}

fn try_extract(lhs: &Level, rhs: &Level) -> Option<(Name, Level)> {
    match (lhs, rhs) {
        (Level::Param(n), o) if !matches!(o, Level::Param(m) if m == n) => {
            Some((n.clone(), o.clone()))
        }
        (o, Level::Param(n)) if !matches!(o, Level::Param(m) if m == n) => {
            Some((n.clone(), o.clone()))
        }
        _ => None,
    }
}

fn level_refs(level: &Level, name: &Name) -> bool {
    match level {
        Level::Zero => false,
        Level::Param(n) => n == name,
        Level::Succ(inner) => level_refs(inner, name),
        Level::Max(a, b) | Level::IMax(a, b) => level_refs(a, name) || level_refs(b, name),
    }
}
