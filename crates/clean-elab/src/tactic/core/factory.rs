// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ProofState factory methods for creating fresh identifiers and constants.
//!
//! Extracted from `core/mod.rs` for file size enforcement (#307).
//! Contains: `fresh_fvar`, `fresh_universe_param`, `mk_const`, `mk_const_str`.

use super::{Goal, ProofState};
use crate::unify::MetaId;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId, Level};
use std::collections::HashSet;

impl ProofState {
    /// Build the exact meta scope shared by elaborator locals and a tactic
    /// goal's local context.
    pub(crate) fn meta_scope_for_context(
        &self,
        local_ctx: &[super::LocalDecl],
    ) -> Vec<(String, FVarId, Expr)> {
        Self::scope_snapshot(&self.elab_locals, local_ctx)
    }

    pub(super) fn scope_snapshot(
        elab_locals: &[super::LocalDecl],
        local_ctx: &[super::LocalDecl],
    ) -> Vec<(String, FVarId, Expr)> {
        let mut seen = HashSet::new();
        let mut locals = Vec::new();
        for decl in elab_locals.iter().chain(local_ctx) {
            if seen.insert(decl.fvar) {
                locals.push((decl.name.clone(), decl.fvar, decl.ty.clone()));
            }
        }
        locals
    }

    /// Create a metavariable for a specific goal context.
    ///
    /// This is required for sibling/derived goals whose local context differs
    /// from the currently focused goal.
    pub(crate) fn fresh_meta_in_context(
        &mut self,
        ty: Expr,
        local_ctx: &[super::LocalDecl],
    ) -> MetaId {
        let locals = self.meta_scope_for_context(local_ctx);
        self.metas.fresh_with_locals(ty, locals)
    }

    /// Create a metavariable with an exact snapshot of the current goal scope.
    ///
    /// Tactic metas must not rely on a later unifier's ambient context: a local
    /// introduced after meta creation would then be indistinguishable from a
    /// local that was genuinely in scope. Capture elaborator locals followed by
    /// the focused goal's locals, de-duplicated by FVarId, at the authority
    /// boundary where the meta is minted.
    pub(crate) fn fresh_meta(&mut self, ty: Expr) -> MetaId {
        let local_ctx = self
            .goals
            .front()
            .map(|goal| goal.local_ctx.clone())
            .unwrap_or_default();
        self.fresh_meta_in_context(ty, &local_ctx)
    }

    /// Create a fresh free variable
    ///
    /// ENSURES: Returned FVarId is unique (not previously returned by this state)
    /// ENSURES: `returned.as_u64() >= self.fvar_base` (tactic-scope, not elaborator-scope)
    /// ENSURES: `self.next_fvar == old(self.next_fvar) + 1`
    pub(crate) fn fresh_fvar(&mut self) -> FVarId {
        let id = FVarId::new(self.next_fvar);
        self.next_fvar += 1;
        id
    }

    /// FVar id the NEXT `intro` on `goal` must allocate — the base of `goal`'s
    /// tactic-binder scope.
    ///
    /// `close_fvars_validated` converts a tactic FVar `n` to a BVar only when
    /// `n` lands in `[fvar_base, fvar_base + binder_depth)`, i.e. it assumes an
    /// introduced FVar's id equals its binder *nesting* depth offset from
    /// `fvar_base`. So a goal's FIRST `intro` must get id `fvar_base`, its second
    /// `fvar_base + 1`, and so on — a quantity that is a pure function of the
    /// goal's own local context, NOT of the monotonic global `next_fvar` counter.
    ///
    /// It is `max(fvar_base, max over goal.local_ctx of (fvar_id + 1))`: one past
    /// the highest tactic-scope FVar already bound in this goal, floored at
    /// `fvar_base`. For a FRESH sibling goal (produced by `constructor` / `apply`
    /// / `refine` — no tactic FVars introduced yet) this is exactly `fvar_base`,
    /// identical across every sibling, so each sibling's first `intro` gets the
    /// same id and maps to the same BVar at the same depth (fixing `;`-sequenced
    /// `intro` on sibling goals, #2533). For single-goal multi-`intro`
    /// (`intro a; intro b`) it is `fvar_base + k` after `k` prior intros, so `b`
    /// correctly follows `a`.
    ///
    /// This is the same quantity `clone_with_goal` / `focus_branch_fvar_base`
    /// compute; factored here so `intro` can reuse it read-only.
    pub(crate) fn goal_fvar_base(&self, goal: &Goal) -> u64 {
        let ctx_floor = goal
            .local_ctx
            .iter()
            .map(|decl| decl.fvar.as_u64() + 1)
            .max()
            .unwrap_or(0);
        ctx_floor.max(self.fvar_base)
    }

    /// Create a fresh universe parameter level.
    ///
    /// Generates a new universe parameter name like `u_0`, `u_1`, etc.
    /// and returns a `Level::Param` with that name. Skips names already
    /// in `universe_params` to avoid collisions.
    /// Part of #1828.
    ///
    /// ENSURES: Returned `Level` is `Level::Param` with a unique name
    /// ENSURES: The name is added to `self.universe_params`
    /// ENSURES: No collision with previously generated universe params
    pub(crate) fn fresh_universe_param(&mut self) -> Level {
        let mut id = self.next_universe;
        let name = loop {
            let candidate = format!("u_{id}");
            id += 1;
            if !self.universe_params.contains(&candidate) {
                break candidate;
            }
        };
        self.next_universe = id;
        self.universe_params.push(name.clone());
        Level::param(Name::from_string(&name))
    }

    /// Build `Expr::const_(name, levels)` with fresh universe params for each
    /// of the constant's declared level parameters.
    ///
    /// This is the correct way to reference a universe-polymorphic constant in
    /// the tactic framework. Calling `Expr::const_(name, vec![])` for a constant
    /// that has universe parameters produces kernel-invalid terms (#1828).
    ///
    /// If the constant is not in the environment, falls back to `vec![]`.
    ///
    /// REQUIRES: `name` is a well-formed Lean name
    /// ENSURES: Returned `Expr` is `Expr::Const(name, levels)` where
    ///   `levels.len() == env.get_const(name).level_params.len()` (or 0 if not found)
    /// ENSURES: Each level in the result is a fresh `Level::Param`
    pub(crate) fn mk_const(&mut self, name: &Name) -> Expr {
        let num_levels = self
            .env
            .get_const(name)
            .map_or(0, |info| info.level_params.len());
        if num_levels > 0 {
            let levels: Vec<Level> = (0..num_levels)
                .map(|_| self.fresh_universe_param())
                .collect();
            Expr::const_(name.clone(), levels)
        } else {
            Expr::const_(name.clone(), vec![])
        }
    }

    /// Build `Expr::const_(name, levels)` for a constant looked up by string name.
    ///
    /// Convenience wrapper around `mk_const` that accepts `&str`.
    /// Part of #1828.
    ///
    /// REQUIRES: `name` is a valid Lean constant name string
    /// ENSURES: Same guarantees as `mk_const`
    pub(crate) fn mk_const_str(&mut self, name: &str) -> Expr {
        self.mk_const(&Name::from_string(name))
    }
}
