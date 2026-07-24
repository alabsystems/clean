// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unification hints for the elaborator.
//!
//! Unification hints allow users to register patterns that guide the unifier
//! when standard unification fails. Each hint specifies a pattern constraint
//! (the trigger) and a sequence of sub-constraints that, when solved, yield
//! a solution for the original unification problem.
//!
//! # Architecture
//!
//! - [`UnificationConstraint`] represents a pair `lhs =?= rhs` to be unified.
//! - [`UnificationHint`] bundles a trigger pattern with ordered sub-constraints.
//! - [`UnificationHintEntry`] adds metadata (name, priority) for registry storage.
//! - [`UnificationHintRegistry`] stores hints indexed by head-symbol pairs for
//!   O(1) lookup during unification.
//!
//! # Lean 4 Reference
//!
//! See `Lean.Meta.UnificationHint` in the Lean 4 source. Hints are registered
//! via the `@[unification_hint]` attribute and are tried when `isDefEq` fails
//! on a rigid-rigid pair.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// A unification constraint: `lhs =?= rhs`.
///
/// Represents the requirement that `lhs` and `rhs` should be definitionally equal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnificationConstraint {
    pub(crate) lhs: Expr,
    pub(crate) rhs: Expr,
}

impl UnificationConstraint {
    /// Create a new unification constraint.
    #[must_use]
    pub(crate) fn new(lhs: Expr, rhs: Expr) -> Self {
        Self { lhs, rhs }
    }
}

/// A unification hint consisting of a trigger pattern and sub-constraints.
///
/// When the unifier encounters `pattern.lhs =?= pattern.rhs` and standard
/// unification fails, it tries to solve the `constraints` in order. If all
/// sub-constraints can be solved, the hint succeeds.
///
/// # Lean 4 Correspondence
///
/// Corresponds to `UnificationHint` in `Lean.Meta.UnificationHint`:
/// ```text
/// structure UnificationHint where
///   pattern     : UnificationConstraint
///   constraints : List UnificationConstraint
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnificationHint {
    pub(crate) pattern: UnificationConstraint,
    pub(crate) constraints: Vec<UnificationConstraint>,
}

impl UnificationHint {
    /// Create a new unification hint.
    #[must_use]
    pub(crate) fn new(
        pattern: UnificationConstraint,
        constraints: Vec<UnificationConstraint>,
    ) -> Self {
        Self {
            pattern,
            constraints,
        }
    }
}

/// Priority for ordering hint application (lower = tried first).
pub(crate) type HintPriority = u32;

/// A registered unification hint with metadata.
#[derive(Debug, Clone)]
pub(crate) struct UnificationHintEntry {
    pub(crate) name: Name,
    pub(crate) priority: HintPriority,
    pub(crate) hint: UnificationHint,
}

impl UnificationHintEntry {
    /// Create a new hint entry.
    #[must_use]
    pub(crate) fn new(name: Name, priority: HintPriority, hint: UnificationHint) -> Self {
        Self {
            name,
            priority,
            hint,
        }
    }
}

/// Key for indexing hints by their head-symbol pair.
///
/// When the unifier sees `f ... =?= g ...`, it looks up hints keyed by `(f, g)`.
/// Hints with a wildcard on one side use `None` for that position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct HeadPairKey {
    lhs_head: Option<Name>,
    rhs_head: Option<Name>,
}

/// Extract the head constant name from an expression.
///
/// Walks through the application spine to find the leftmost non-App node,
/// then returns the constant name if it is a `Const`.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `Some(name)` if head is `Const(name, _)`, `None` otherwise
fn head_const_name(expr: &Expr) -> Option<&Name> {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        Some(name)
    } else {
        None
    }
}

/// Registry of unification hints indexed by head-symbol pairs.
///
/// Hints are stored in a `HashMap` keyed by the head constants of the
/// pattern's LHS and RHS. Within each bucket, hints are sorted by priority
/// (ascending — lower priority values are tried first).
///
/// # Thread Safety
///
/// Uses `Arc<[UnificationHintEntry]>` for cheap cloning of hint lists.
#[derive(Debug, Clone, Default)]
pub(crate) struct UnificationHintRegistry {
    hints: HashMap<HeadPairKey, Vec<Arc<UnificationHintEntry>>>,
}

impl UnificationHintRegistry {
    /// Create an empty registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            hints: HashMap::new(),
        }
    }

    /// Register a unification hint.
    ///
    /// The hint is indexed by the head constants of its pattern's LHS and RHS.
    /// After insertion the bucket is re-sorted by priority (ascending).
    ///
    /// REQUIRES: `entry` has a well-formed hint with valid pattern expressions
    /// ENSURES: The hint is retrievable via `lookup` with matching head symbols
    pub(crate) fn register_hint(&mut self, entry: UnificationHintEntry) {
        let key = HeadPairKey {
            lhs_head: head_const_name(&entry.hint.pattern.lhs).cloned(),
            rhs_head: head_const_name(&entry.hint.pattern.rhs).cloned(),
        };
        let entry = Arc::new(entry);
        let bucket = self.hints.entry(key).or_default();
        bucket.push(entry);
        bucket.sort_by_key(|e| e.priority);
    }

    /// Look up hints applicable to a `lhs =?= rhs` constraint.
    ///
    /// Returns hints whose pattern head symbols match the head constants of
    /// the given expressions. Results are returned in priority order (ascending).
    ///
    /// REQUIRES: `lhs` and `rhs` are well-formed Lean expressions
    /// ENSURES: Returned slice is sorted by ascending priority
    /// ENSURES: Returns empty slice when no hints match
    pub(crate) fn lookup(&self, lhs: &Expr, rhs: &Expr) -> &[Arc<UnificationHintEntry>] {
        let key = HeadPairKey {
            lhs_head: head_const_name(lhs).cloned(),
            rhs_head: head_const_name(rhs).cloned(),
        };
        self.hints.get(&key).map_or(&[], |v| v.as_slice())
    }

    /// Return the total number of registered hints.
    #[must_use]
    pub(crate) fn hint_count(&self) -> usize {
        self.hints.values().map(|v| v.len()).sum()
    }
}

/// Attempt to apply unification hints to solve `lhs =?= rhs`.
///
/// Iterates over registered hints whose head symbols match, and for each hint
/// attempts to match the pattern against the given expressions. On the first
/// successful match, returns the sub-constraints that the caller must solve.
///
/// # Pattern Matching
///
/// A hint pattern matches when both LHS and RHS structurally align with the
/// given expressions at the head-symbol level. BVar positions in the pattern
/// are treated as wildcards (metavariables to be instantiated).
///
/// REQUIRES: `registry` contains well-formed hints
/// REQUIRES: `lhs` and `rhs` are well-formed Lean expressions
/// ENSURES: Returns `Some(constraints)` on first matching hint
/// ENSURES: Returns `None` when no hint matches
#[must_use]
pub(crate) fn try_unification_hints(
    registry: &UnificationHintRegistry,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Vec<UnificationConstraint>> {
    let candidates = registry.lookup(lhs, rhs);
    for entry in candidates {
        if let Some(constraints) = try_match_hint(&entry.hint, lhs, rhs) {
            return Some(constraints);
        }
    }
    None
}

/// Try to match a single hint pattern against `lhs =?= rhs`.
///
/// The pattern is matched structurally: application spines must have the same
/// head and arity, constants must match by name, and BVar positions in the
/// pattern act as wildcards that capture the corresponding sub-expression
/// from the input.
///
/// On success, the captured bindings are substituted into the hint's
/// sub-constraints and the resulting constraints are returned.
///
/// REQUIRES: `hint` is well-formed
/// ENSURES: Returns `None` if pattern does not match structurally
/// ENSURES: On `Some`, returned constraints have pattern BVars replaced
///          with captured sub-expressions
fn try_match_hint(
    hint: &UnificationHint,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Vec<UnificationConstraint>> {
    let mut bindings: HashMap<u32, Expr> = HashMap::new();
    if !match_expr(&hint.pattern.lhs, lhs, &mut bindings) {
        return None;
    }
    if !match_expr(&hint.pattern.rhs, rhs, &mut bindings) {
        return None;
    }
    // Substitute captured bindings into sub-constraints
    let constraints = hint
        .constraints
        .iter()
        .map(|c| UnificationConstraint {
            lhs: substitute_bindings(&c.lhs, &bindings),
            rhs: substitute_bindings(&c.rhs, &bindings),
        })
        .collect();
    Some(constraints)
}

/// Structurally match a pattern expression against a concrete expression,
/// collecting BVar → Expr bindings.
///
/// Pattern BVars act as wildcards: they capture the corresponding sub-expression.
/// If a BVar index was previously bound, the new capture must be structurally
/// equal to the existing binding.
///
/// REQUIRES: `pattern` and `expr` are well-formed expressions
/// ENSURES: Returns `true` iff the structure matches, updating `bindings`
/// ENSURES: On `false`, `bindings` may be partially updated (caller discards)
fn match_expr(pattern: &Expr, expr: &Expr, bindings: &mut HashMap<u32, Expr>) -> bool {
    match pattern.kind() {
        ExprKind::BVar(idx) => {
            if let Some(existing) = bindings.get(idx) {
                existing == expr
            } else {
                bindings.insert(*idx, expr.clone());
                true
            }
        }
        ExprKind::Const(pn, pls) => {
            matches!(expr.kind(), ExprKind::Const(en, els) if pn == en && pls == els)
        }
        ExprKind::App(pf, pa) => {
            if let ExprKind::App(ef, ea) = expr.kind() {
                match_expr(pf, ef, bindings) && match_expr(pa, ea, bindings)
            } else {
                false
            }
        }
        ExprKind::Sort(pl) => matches!(expr.kind(), ExprKind::Sort(el) if pl == el),
        ExprKind::FVar(pf) => matches!(expr.kind(), ExprKind::FVar(ef) if pf == ef),
        ExprKind::Lit(pl) => matches!(expr.kind(), ExprKind::Lit(el) if pl == el),
        _ => match_expr_compound(pattern, expr, bindings),
    }
}

/// Match compound expressions (binders, let, proj, mdata).
fn match_expr_compound(pattern: &Expr, expr: &Expr, bindings: &mut HashMap<u32, Expr>) -> bool {
    match pattern.kind() {
        ExprKind::Pi(pb, pt, pbo) => {
            if let ExprKind::Pi(eb, et, ebo) = expr.kind() {
                pb == eb && match_expr(pt, et, bindings) && match_expr(pbo, ebo, bindings)
            } else {
                false
            }
        }
        ExprKind::Lam(pb, pt, pbo) => {
            if let ExprKind::Lam(eb, et, ebo) = expr.kind() {
                pb == eb && match_expr(pt, et, bindings) && match_expr(pbo, ebo, bindings)
            } else {
                false
            }
        }
        ExprKind::Let(_, pt, pv, pbo, _) => {
            if let ExprKind::Let(_, et, ev, ebo, _) = expr.kind() {
                match_expr(pt, et, bindings)
                    && match_expr(pv, ev, bindings)
                    && match_expr(pbo, ebo, bindings)
            } else {
                false
            }
        }
        ExprKind::Proj(pn, pi, pe) => {
            if let ExprKind::Proj(en, ei, ee) = expr.kind() {
                pn == en && pi == ei && match_expr(pe, ee, bindings)
            } else {
                false
            }
        }
        ExprKind::MData(_, pinner) => {
            if let ExprKind::MData(_, einner) = expr.kind() {
                match_expr(pinner, einner, bindings)
            } else {
                false
            }
        }
        _ => pattern == expr,
    }
}

/// Substitute captured BVar bindings into an expression.
///
/// Replaces each `BVar(idx)` with its binding from the map. Unbound BVars
/// are left in place (they represent uncaptured pattern variables).
///
/// REQUIRES: `bindings` contains well-formed expressions
/// ENSURES: All BVars present in `bindings` are replaced
fn substitute_bindings(expr: &Expr, bindings: &HashMap<u32, Expr>) -> Expr {
    match expr.kind() {
        ExprKind::BVar(idx) => {
            if let Some(bound) = bindings.get(idx) {
                bound.clone()
            } else {
                expr.clone()
            }
        }
        ExprKind::App(f, a) => {
            let new_f = substitute_bindings(f, bindings);
            let new_a = substitute_bindings(a, bindings);
            Expr::app(new_f, new_a)
        }
        ExprKind::Pi(bd, ty, body) => {
            let new_ty = substitute_bindings(ty, bindings);
            let new_body = substitute_bindings(body, bindings);
            Expr::pi(*bd, new_ty, new_body)
        }
        ExprKind::Lam(bd, ty, body) => {
            let new_ty = substitute_bindings(ty, bindings);
            let new_body = substitute_bindings(body, bindings);
            Expr::lam(*bd, new_ty, new_body)
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let new_ty = substitute_bindings(ty, bindings);
            let new_val = substitute_bindings(val, bindings);
            let new_body = substitute_bindings(body, bindings);
            Expr::from_kind(ExprKind::Let(
                name.clone(),
                Arc::new(new_ty),
                Arc::new(new_val),
                Arc::new(new_body),
                *non_dep,
            ))
        }
        ExprKind::Proj(name, idx, inner) => {
            let new_inner = substitute_bindings(inner, bindings);
            Expr::from_kind(ExprKind::Proj(name.clone(), *idx, Arc::new(new_inner)))
        }
        ExprKind::MData(md, inner) => {
            let new_inner = substitute_bindings(inner, bindings);
            Expr::from_kind(ExprKind::MData(md.clone(), Arc::new(new_inner)))
        }
        // Const, Sort, FVar, Lit, and other leaf nodes: no BVars to substitute
        _ => expr.clone(),
    }
}
