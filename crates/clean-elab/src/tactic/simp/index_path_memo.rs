// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discrimination-tree paths of CLOSED simp-lemma patterns, carried from one
//! build of the cached simp set to the next.
//!
//! # Why
//!
//! `cache.rs` keeps the built [`super::types::SimpLemmaSet`] across `simp`
//! calls and rebuilds it whenever the simp REGISTRY changes — correctly, since
//! a lemma that became `@[simp]` must be seen by the next call. But every
//! `@[simp]` declaration of the file under check is such a change
//! (`Mathlib/Logic/Basic.lean` carries 34, `Mathlib/Logic/Function/Basic.lean`
//! 28, `Mathlib/Order/Basic.lean` 26), and each rebuild re-derived the key path
//! of all ~10k imported lemmas, one budgeted `whnf` per expression node. The
//! performance audit's `sample` of `Mathlib/Logic/Basic.lean` at t = 290 s put
//! 27% of the process in that rebuild (`collect_simp_lemmas` →
//! `SimpLemmaSet::with_goal` → `push_expr`, 95% of it path computation).
//!
//! # What is reused, and why it is the same set
//!
//! Only the path of a pattern with NO free variables (no goal locals and no
//! metavariables, which are free variables here) is memoised, keyed by the
//! pattern itself and its index mode. Such a path is exactly what the cached
//! set already relies on (`cache.rs`, "Goal independence of the cached tree"):
//! `mk_path` on a closed term cannot observe the goal's context, and constants
//! the pattern names are never redefined. So a rebuild that takes a remembered
//! path inserts the same keys in the same order as one that recomputes it, and
//! produces the same set; only the paths of lemmas NEW since the last build
//! are computed. A pattern with a free variable (a hypothesis or `simp [e]`
//! term lemma) never reaches the memo.
//!
//! The memo travels with the cache entries it was built for (`cache.rs` seeds
//! each rebuild from a recent entry with the same environment origin), so it
//! lives and dies with the set cache and carries no assumption that cache does
//! not already make.
//! A remembered path can only change which lemmas are OFFERED; every rewrite
//! is still re-checked by the matcher, the `lhs_inst ≡ expr` guard and the
//! kernel.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::Expr;

use crate::tactic::discr_tree::{mk_path, DiscrKey, IndexMode};
use crate::tactic::{Goal, ProofState};

/// The keys one lemma is inserted under: its pattern's path and, when the
/// matcher's projection peel spells the pattern differently, that path too.
#[derive(Debug)]
pub(crate) struct LemmaPaths {
    pub(crate) path: Vec<DiscrKey>,
    pub(crate) peeled: Option<Vec<DiscrKey>>,
}

/// Remembered [`LemmaPaths`] of closed patterns.
#[derive(Debug, Default, Clone)]
pub(crate) struct PathMemo {
    entries: HashMap<(Expr, IndexMode), Arc<LemmaPaths>>,
}

impl PathMemo {
    /// The paths of `lhs` under `mode`: remembered when `lhs` is closed and
    /// was seen before, computed (and, when closed, remembered) otherwise.
    pub(crate) fn paths(
        &mut self,
        state: &ProofState,
        goal: &Goal,
        lhs: &Expr,
        mode: IndexMode,
    ) -> Arc<LemmaPaths> {
        if lhs.has_fvar_quick() {
            return Arc::new(compute_lemma_paths(state, goal, lhs, mode));
        }
        Arc::clone(
            self.entries
                .entry((lhs.clone(), mode))
                .or_insert_with(|| Arc::new(compute_lemma_paths(state, goal, lhs, mode))),
        )
    }
}

/// The keys `SimpLemmaSet::with_goal` inserts a lemma under, computed.
pub(crate) fn compute_lemma_paths(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    mode: IndexMode,
) -> LemmaPaths {
    #[cfg(test)]
    PATH_COMPUTATIONS.with(|count| count.set(count.get() + 1));
    let path = mk_path(state, goal, lhs, mode);
    // ALSO the PEELED spelling of the LHS — see `SimpLemmaSet::with_goal` for
    // why the index must meet the matcher's own projection normalization.
    let peeled = crate::tactic::op_projection::reduce_op_projection_head(state, goal, lhs)
        .map(|peeled| mk_path(state, goal, &peeled, mode))
        .filter(|peeled_path| *peeled_path != path);
    LemmaPaths { path, peeled }
}

#[cfg(test)]
thread_local! {
    static PATH_COMPUTATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Test-only: how many lemma key paths this thread has COMPUTED (a memo hit
/// computes none).
#[cfg(test)]
pub(crate) fn path_computation_count() -> usize {
    PATH_COMPUTATIONS.with(std::cell::Cell::get)
}
