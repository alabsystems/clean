// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A declaration binder a tactic CONSUMED is out of scope for the terms later
//! tactics elaborate.
//!
//! A `by` block's goal starts with every enclosing `ElabCtx` local
//! (`ProofState::elab_locals`), and those locals stay on the `ElabCtx` stack
//! for the whole block. When a tactic removes one from the goal — `clear h`,
//! `subst h`, `cases h` on an equation (which eliminates `h` and a side
//! variable), `cases x` — Lean's goal no longer has it, so a later `exact h`
//! is "unknown identifier 'h'" and a `?_` hole cannot capture it. Clean kept
//! resolving the stale binder by name: `clear h; exact h` was ACCEPTED where
//! pinned Lean 4.8.0 refuses it, and a `refine ⟨?_, ?_⟩` after `subst` minted
//! a fresh local for the consumed binder its holes captured and failed its
//! own scope check (`Sem.bindFreshPair_ok`, trust-ir `Semantics/Monad.lean`,
//! once `cases h` unified its equation — G82). Every tactic term is now
//! elaborated with those binders hidden; they come back when the tactic ends.

use super::local_bindings::LocalEntry;
use super::ElabCtx;
use crate::tactic::{self, ProofState};
use clean_kernel::{Expr, FVarId};
use std::collections::{HashMap, HashSet};

/// The `ElabCtx` locals as they were before [`ElabCtx::hide_consumed_binders`].
pub(super) struct HiddenBinders {
    entries: Vec<LocalEntry>,
    let_values: HashMap<FVarId, Expr>,
    binder_infos: HashMap<FVarId, clean_kernel::BinderData>,
}

impl ElabCtx<'_> {
    /// Take out of `self.locals` every declaration binder of the block
    /// (`ps.elab_locals`) that `goal` no longer holds. Returns what to restore,
    /// or `None` when nothing was hidden.
    pub(super) fn hide_consumed_binders(
        &mut self,
        ps: &ProofState,
        goal: &tactic::Goal,
    ) -> Option<HiddenBinders> {
        let in_goal: HashSet<FVarId> = goal.local_ctx.iter().map(|d| d.fvar).collect();
        // An auxiliary declaration (a `mutual` sibling, a `let rec` / `where`
        // helper) is not in the goal's visible context because the tactic
        // bridge took it out (brick B6, `docs/DECISIONS.md` R66), not because
        // a tactic consumed it: a term still names it, as in Lean.
        let mut consumed: HashSet<FVarId> = ps
            .elab_locals
            .iter()
            .map(|d| d.fvar)
            .filter(|fvar| !in_goal.contains(fvar) && !self.aux_decl_locals.contains(fvar))
            .collect();
        // ... unless its TYPE names a consumed local: Lean reverts with
        // `clearAuxDeclsInsteadOfRevert`, which drops such an auxiliary
        // declaration, so `subst h; exact helper` with `helper : P n` is
        // "unknown identifier 'helper'" (review r6, X4). To a fixpoint, so an
        // auxiliary declaration naming a dropped one is dropped too.
        loop {
            let dropped: Vec<FVarId> = self
                .locals
                .iter()
                .filter(|(_, fvar, ty)| {
                    self.aux_decl_locals.contains(fvar)
                        && !consumed.contains(fvar)
                        && consumed.iter().any(|gone| mentions_fvar(ty, *gone))
                })
                .map(|(_, fvar, _)| *fvar)
                .collect();
            if dropped.is_empty() {
                break;
            }
            consumed.extend(dropped);
        }
        if !self
            .locals
            .iter()
            .any(|(_, fvar, _)| consumed.contains(fvar))
        {
            return None;
        }
        let hidden = HiddenBinders {
            entries: self.locals.to_vec(),
            let_values: self.locals.let_values().clone(),
            binder_infos: self.locals.binder_infos().clone(),
        };
        self.locals.retain(|(_, fvar, _)| !consumed.contains(fvar));
        Some(hidden)
    }

    /// Put back exactly the locals [`Self::hide_consumed_binders`] saw.
    pub(super) fn restore_hidden_binders(&mut self, hidden: HiddenBinders) {
        self.locals
            .restore(hidden.entries, hidden.let_values, hidden.binder_infos);
    }
}

/// Whether `expr` mentions the local `id`.
fn mentions_fvar(expr: &Expr, id: FVarId) -> bool {
    tactic::hypothesis::collect_fvars(expr).contains(&id)
}
