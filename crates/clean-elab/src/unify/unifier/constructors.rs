// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`Unifier`] constructors, one per reduction transparency (split from
//! `mod.rs`).

use clean_kernel::{Environment, LocalContext, TypeChecker};
use std::cell::{Cell, RefCell};

use super::Unifier;
use crate::unify::meta_state::MetaState;

impl<'a> Unifier<'a> {
    /// Create a unifier without WHNF support (legacy)
    ///
    /// This constructor is kept for backwards compatibility with tests.
    /// For production use, prefer `with_env` which enables WHNF reduction.
    pub fn new(metas: &'a mut MetaState) -> Self {
        Self {
            metas,
            tc_cache: RefCell::new(None),
            env: None,
            protect_heads: false,
            initial_context_len: 0,
            rigid_congruence_context: Cell::new(None),
            check_types_depth: Cell::new(0),
            unreduced_failures: Cell::new(0),
        }
    }

    /// Create a unifier with environment for WHNF reduction
    ///
    /// This enables proper WHNF reduction during unification, which is
    /// required for correctly handling beta/delta/iota/zeta reductions.
    pub fn with_env(metas: &'a mut MetaState, env: &'a Environment, ctx: LocalContext) -> Self {
        let initial_context_len = ctx.len();
        // Pre-create the TypeChecker so the WHNF cache persists across calls
        let tc = TypeChecker::with_context(env, ctx);
        // B14: unification-time WHNF/def-eq honors reducibility hints, so an
        // `@[irreducible]` definition stays folded when the unifier reduces
        // rigid heads (e.g. matching `rfl`'s `f =?= v`). Matches MetaM
        // `canUnfold` at `.default`; the kernel's final check stays blind.
        tc.set_honor_reducibility(true);
        Self {
            metas,
            tc_cache: RefCell::new(Some(tc)),
            env: Some(env),
            protect_heads: false,
            initial_context_len,
            rigid_congruence_context: Cell::new(None),
            check_types_depth: Cell::new(0),
            unreduced_failures: Cell::new(0),
        }
    }

    /// Create a unifier that reduces at `withReducible` transparency (B15).
    ///
    /// Like [`Unifier::with_env`], but the WHNF/def-eq path unfolds ONLY
    /// `@[reducible]` (abbreviation) constants — `Regular` (semireducible),
    /// `@[irreducible]`, and theorem heads stay folded, matching MetaM
    /// `withReducible` / `canUnfold` at `.reducible`. `simp` uses this when
    /// matching lemma LHSs against a target so that a bare `def f := e`
    /// (semireducible) is opaque to lemma matching, exactly as in Lean 4's
    /// `simp` (`Lean/Meta/Tactic/Simp` runs at reducible transparency).
    ///
    /// Strictly narrowing relative to [`Unifier::with_env`]: it can only turn a
    /// former (semireducible-unfolding) match into a non-match.
    pub(crate) fn with_env_reducible(
        metas: &'a mut MetaState,
        env: &'a Environment,
        ctx: LocalContext,
    ) -> Self {
        let initial_context_len = ctx.len();
        let mut tc = TypeChecker::with_context(env, ctx);
        tc.set_transparency(clean_kernel::TransparencyMode::Reducible);
        tc.set_honor_reducibility(true);
        Self {
            metas,
            tc_cache: RefCell::new(Some(tc)),
            env: Some(env),
            protect_heads: false,
            initial_context_len,
            rigid_congruence_context: Cell::new(None),
            check_types_depth: Cell::new(0),
            unreduced_failures: Cell::new(0),
        }
    }

    /// Create a unifier that reduces at Lean's `.instances` transparency
    /// (G47): only `@[reducible]` constants and registered instances unfold.
    ///
    /// Instance synthesis runs at this transparency in Lean
    /// (`Lean/Meta/SynthInstance.lean`), so a candidate `Monad Option` does
    /// not match a goal `Monad M` for a plain `def M a := Option a` — Lean
    /// answers "failed to synthesize instance Monad M". Strictly narrowing
    /// relative to [`Unifier::with_env`].
    pub(crate) fn with_env_instances(
        metas: &'a mut MetaState,
        env: &'a Environment,
        ctx: LocalContext,
    ) -> Self {
        let initial_context_len = ctx.len();
        let mut tc = TypeChecker::with_context(env, ctx);
        tc.set_transparency(clean_kernel::TransparencyMode::Instances);
        tc.set_honor_reducibility(true);
        Self {
            metas,
            tc_cache: RefCell::new(Some(tc)),
            env: Some(env),
            protect_heads: false,
            initial_context_len,
            rigid_congruence_context: Cell::new(None),
            check_types_depth: Cell::new(0),
            unreduced_failures: Cell::new(0),
        }
    }
}
