// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant instantiation, unfolding, and definition height computation.
//!
//! Extracted from env/mod.rs for maintainability (see #307).
//! Contains methods for instantiating constant types with universe levels,
//! unfolding reducible constants, and computing definition heights.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

use super::types::{Reducibility, TransparencyMode};
use super::Environment;

/// Apply universe level substitution to an expression.
///
/// Given parallel slices of parameter names and replacement levels,
/// substitutes each `Level::Param(name)` in `expr` with the corresponding level.
/// Returns `expr.clone()` when `params` is empty (no-op fast path).
///
/// REQUIRES: `params.len() == levels.len()` (caller enforces this)
fn apply_level_subst(expr: &Expr, params: &[Name], levels: &[Level]) -> Expr {
    // No length assertion needed: this is provably panic-free regardless of the
    // relative lengths. Every caller (`instantiate_type`/`unfold`) returns `None` on
    // a mismatch, so the contract holds; and the substitution itself
    // (`Level::substitute_slice` => `params.iter().zip(levels.iter())`) truncates to
    // the shorter slice — it never indexes out of bounds. So no skip / cfg-gate /
    // contract is required; the verifier discharges it directly.
    if params.is_empty() {
        return expr.clone();
    }
    expr.instantiate_level_params_direct(params, levels)
}

impl Environment {
    /// Instantiate a constant's type with universe levels.
    ///
    /// Returns `None` if the constant is not found OR if the number of supplied
    /// levels does not match the constant's declared level parameters (#1277).
    ///
    /// ENSURES: Returns `Some(type)` only when `levels.len() == info.level_params.len()`
    /// REQUIRES: none
    pub fn instantiate_type(&self, name: &Name, levels: &[Level]) -> Option<Expr> {
        let info = self.get_const(name)?;
        // Enforce level parameter count match — reject silent truncation (#1277)
        if info.level_params.len() != levels.len() {
            return None;
        }
        Some(apply_level_subst(&info.type_, &info.level_params, levels))
    }

    /// Compute the definition height of an expression value.
    ///
    /// Walks all sub-expressions and finds the maximum height of any referenced
    /// constant. The caller should add 1 to get the new definition's height.
    ///
    /// Reference: Lean 4 `declaration.cpp:193-208` `get_max_height`
    pub(crate) fn get_max_height(&self, value: &Expr) -> u32 {
        let mut max_h: u32 = 0;
        let mut stack: Vec<&Expr> = vec![value];
        // INVARIANT: *const Expr is used as HashSet key for O(1) cycle/revisit
        // detection. This is sound because all Expr sub-expressions are stored
        // behind Arc<Expr> (see ExprKind variants), which heap-allocates and
        // never moves the inner Expr. The visited set lives only for this call,
        // and the input `value` reference (plus Arc refcounts) keeps all
        // sub-expression addresses stable throughout the traversal.
        let mut visited: hashbrown::HashSet<*const Expr> = hashbrown::HashSet::new();
        while let Some(e) = stack.pop() {
            if !visited.insert(e as *const Expr) {
                continue;
            }
            match e.kind() {
                ExprKind::Const(name, _) => {
                    if let Some(info) = self.get_const(name) {
                        let h = info.reducibility.height();
                        if h > max_h {
                            max_h = h;
                        }
                    }
                }
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(ty);
                    stack.push(body);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push(ty);
                    stack.push(val);
                    stack.push(body);
                }
                ExprKind::Proj(_, _, e_inner) => {
                    stack.push(e_inner);
                }
                ExprKind::MData(_, e_inner) => {
                    stack.push(e_inner);
                }
                // Squash, cubical extensions — recurse into sub-expressions
                ExprKind::Squash(inner) => stack.push(inner),
                ExprKind::CubicalPathLam { body } => stack.push(body),
                ExprKind::CubicalPathApp { path, arg } => {
                    stack.push(path);
                    stack.push(arg);
                }
                ExprKind::CubicalPath { ty, left, right } => {
                    stack.push(ty);
                    stack.push(left);
                    stack.push(right);
                }
                ExprKind::CubicalHComp { ty, phi, u, base } => {
                    stack.push(ty);
                    stack.push(phi);
                    stack.push(u);
                    stack.push(base);
                }
                ExprKind::CubicalTransp { ty, phi, base } => {
                    stack.push(ty);
                    stack.push(phi);
                    stack.push(base);
                }
                ExprKind::CubicalCoe { ty, r, s, base } => {
                    stack.push(ty);
                    stack.push(r);
                    stack.push(s);
                    stack.push(base);
                }
                // BVar, FVar, Sort, Lit, SProp, CubicalInterval/I0/I1 — leaf nodes
                _ => {}
            }
        }
        max_h
    }

    /// Get the value of a reducible constant with universe levels substituted.
    ///
    /// Returns `None` if the constant is not found, not reducible, has no value,
    /// or if `levels.len()` does not match the declared level parameter count (#1277).
    ///
    /// ENSURES: Returns `Some(value)` only when `levels.len() == info.level_params.len()`
    /// REQUIRES: none
    pub fn unfold(&self, name: &Name, levels: &[Level]) -> Option<Expr> {
        let info = self.get_const(name)?;
        if info.reducibility != Reducibility::Reducible {
            return None;
        }
        let value = info.value.as_ref()?;
        // Enforce level parameter count match — reject silent truncation (#1277)
        if info.level_params.len() != levels.len() {
            return None;
        }
        Some(apply_level_subst(value, &info.level_params, levels))
    }

    /// Unfold a constant's definition for kernel type checking.
    ///
    /// Matches Lean 4's kernel `unfold_definition_core`: unfolds any constant
    /// that has a value and is a definition or theorem, but NOT opaque
    /// declarations. The kernel type checker has no transparency modes; it
    /// unfolds freely. Reducibility hints only control unfolding ORDER in the
    /// lazy delta loop, not WHETHER a constant can be unfolded.
    ///
    /// Reference: Lean 4 `type_checker.cpp:497` `unfold_definition_core` +
    /// `declaration.h:466` `has_value(false)` (returns true for definitions
    /// and theorems, false for opaque/axiom).
    ///
    /// Returns `None` if:
    /// - Constant not found
    /// - Constant has no value (axiom)
    /// - Constant is an opaque declaration (`ConstantKind::Opaque`)
    /// - Level count mismatch (#1277)
    pub(crate) fn unfold_definition(&self, name: &Name, levels: &[Level]) -> Option<Expr> {
        let info = self.get_const(name)?;

        // Match Lean 4: has_value(false) returns true for Definition and Theorem,
        // false for Opaque and Axiom. Axioms have value=None so the check below
        // handles them. Opaque declarations have value=Some but must not unfold.
        if info.kind == super::types::ConstantKind::Opaque {
            return None;
        }

        let value = info.value.as_ref()?;
        // Enforce level parameter count match — reject silent truncation (#1277)
        if info.level_params.len() != levels.len() {
            return None;
        }
        Some(apply_level_subst(value, &info.level_params, levels))
    }

    /// Get the value of a constant with transparency control.
    ///
    /// Unlike `unfold`, this respects the `TransparencyMode` and `Reducibility`:
    /// - `Reducible`: Only unfolds constants marked as `Reducibility::Reducible`
    /// - `Instances`: Unfolds Reducible + Semireducible + registered instances
    /// - `Default`: Unfolds everything except `Reducibility::Irreducible`/`Opaque`
    /// - `All`: Unfolds everything including irreducible constants (but never opaque)
    ///
    /// Returns `None` if level count mismatches the declaration (#1277).
    ///
    /// ENSURES: Returns `Some(value)` only when `levels.len() == info.level_params.len()`
    /// REQUIRES: none
    pub(crate) fn unfold_with_transparency(
        &self,
        name: &Name,
        levels: &[Level],
        mode: TransparencyMode,
    ) -> Option<Expr> {
        let info = self.get_const(name)?;

        // Check if unfolding is allowed at this transparency level
        // Special case for Instances mode: also unfold registered instances.
        // Opaque/theorem declarations never unfold, even if registered as instances.
        let should_unfold = info.reducibility.should_unfold(mode)
            || (mode == TransparencyMode::Instances
                && self.is_instance(name)
                && info.reducibility != Reducibility::Opaque);
        if !should_unfold {
            return None;
        }

        let value = info.value.as_ref()?;
        // Enforce level parameter count match — reject silent truncation (#1277)
        if info.level_params.len() != levels.len() {
            return None;
        }
        Some(apply_level_subst(value, &info.level_params, levels))
    }
}
