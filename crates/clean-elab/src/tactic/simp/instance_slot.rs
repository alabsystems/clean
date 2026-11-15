// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typeclass synthesis for a simp lemma binder the left-hand side leaves open.
//!
//! # Lean's rule
//!
//! `synthesizeArgs` (`Lean/Meta/Tactic/Simp/Rewrite.lean:57-100`) fills an
//! unassigned argument by `trySynthInstance` whenever `isClass? type` holds,
//! and `isClass?` (`Lean/Meta/Basic.lean`, `isClassQuick?` /
//! `isClassExpensive?`) reads the class off the CONCLUSION of the type's `∀`
//! telescope, unfolding reducible definitions on the way. So each of
//!
//! * `[Decidable q]` — a class application,
//! * `[∀ n, Decidable (p n)]` — a telescope ending in one
//!   (`Decidable.not_forall`), and
//! * `[DecidablePred p]` — a reducible alias of such a telescope
//!
//! is an instance slot. Clean recognised the first spelling only, so a lemma
//! with a `∀`-quantified instance binder made no progress even with the
//! instance in the local context (measured 2026-09-20 on the pinned
//! v4.30.0-rc2 binary: `lemPi (p : Nat → Prop) [∀ n, Decidable (p n)] :
//! QQ (∀ n, p n) ↔ True` rewrites there from a local and from a global
//! instance alike). The test itself is [`crate::infer::class_goal`], shared
//! with the rule that makes a class-typed LOCAL a local instance of the query.

use clean_kernel::{Expr, FVarId};

use super::budget::SimpBudget;
use crate::tactic::core::{Goal, ProofState};

/// Typeclass synthesis for an undetermined lemma binder of type `slot_ty`, or
/// `None` (not a class, or no instance).
///
/// Lean's `synthesizeArgs.synthesizeInstance`: `trySynthInstance` in the
/// goal's local context, and the answer is kept only when it inhabits the
/// slot (`isDefEq x val`). Answers are memoised per traversal and per local
/// context ([`SimpBudget::memo_instance`] — a binder simp has opened can be
/// the instance, so the same class goal has different answers at different
/// depths); the type check below runs on every use, so a memoised answer can
/// never be installed in a slot it does not fit.
///
/// # Soundness
///
/// Nothing is fabricated: the instance comes from the elaborator's resolver
/// ([`crate::infer::ElabCtx::synthesize_in_tactic_scope`]), it is refused
/// unless its inferred type is def-eq to `slot_ty` AS THE LEMMA STATES IT
/// (never merely to the unfolded form the resolver was asked), and the
/// finished proof is re-checked by the kernel.
pub(super) fn synthesize_class_slot(
    state: &ProofState,
    goal: &Goal,
    slot_ty: &Expr,
    budget: &SimpBudget,
) -> Option<Expr> {
    let class_ty = crate::infer::class_goal(&state.env, state.instances.as_ref(), slot_ty)?;
    let scope: Vec<FVarId> = goal.local_ctx.iter().map(|decl| decl.fvar).collect();
    let found = budget.memo_instance(&scope, &class_ty, || {
        let scope = crate::infer::TacticInstanceScope {
            instances: state.instances.as_ref(),
            namespace_state: state.namespace_state(),
            visibility: state.instance_visibility.as_deref(),
            rigid_levels: state.metas.rigid_level_params_snapshot(),
            locals: state
                .meta_scope_for_context(&goal.local_ctx)
                .into_iter()
                .map(|(name, fvar, ty)| {
                    let ty = state.metas.instantiate(&ty);
                    (name, fvar, ty)
                })
                .collect(),
            next_fvar: state.next_fvar,
            level_mint: state.level_mint.clone(),
        };
        crate::infer::ElabCtx::synthesize_in_tactic_scope(&state.env, &scope, &class_ty)
    })?;
    state
        .infer_type(goal, &found)
        .is_ok_and(|ty| state.is_def_eq(goal, &ty, slot_ty))
        .then_some(found)
}
