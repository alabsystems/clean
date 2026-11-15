// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A hypothesis that `simp … at h` simplifies to `False` closes the goal.
//!
//! # Lean's rule
//!
//! `applySimpResult` (`Lean/Meta/Tactic/Simp/Main.lean`), with
//! `mayCloseGoal := true` — the default of `simp at h`, `simp at h₁ h₂ ⊢`,
//! `simp at *` and `simp_all` — assigns the goal
//! `False.elim (Eq.mp eqProof h)` when the simplified type `isFalse`, and
//! returns `none`: the goal is CLOSED, later locations are not visited.
//!
//! # What Clean did instead
//!
//! `simp_at_with_lemmas` always replaced the hypothesis and handed the goal
//! back, so `simp only [lemN] at h` with `lemN : ¬ QQ n` and `h : QQ n` left
//! `h : False ⊢ 1 = 2` as an unsolved goal where Lean is finished (measured
//! 2026-09-20 on prelude replicas; found while landing the global `¬p ↦
//! p = False` rule, which is what makes a hypothesis reach `False` from a
//! plain negation lemma).
//!
//! The test is on the RESULT, so a hypothesis that already is `False` closes
//! the goal too (`simp at h` with `h : False` is not "no progress" in Lean).
//!
//! # Soundness
//!
//! Nothing is trusted: the term is `@False.elim.{u} target h'` with `h'` the
//! cast `simp at` already builds for the rewritten hypothesis, and it goes
//! through the checked `close_goal` (strict inference plus a def-eq check
//! against the target). When that check refuses it the caller falls back to
//! the ordinary replace-the-hypothesis path, so this can only ever close a
//! goal the kernel agrees is closed.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::proof::get_sort_level;
use crate::tactic::{Goal, ProofState};

/// Whether `e` is the proposition `False` (Lean's `Expr.isFalse`).
fn is_false_prop(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels)
        if levels.is_empty() && *name == Name::from_string("False"))
}

/// Close `goal` from `false_proof : new_ty` when `new_ty` is `False`.
///
/// ENSURES: `true` iff the goal was closed by the checked `close_goal`; on
///   `false` the proof state is unchanged.
pub(super) fn close_goal_by_false_hypothesis(
    state: &mut ProofState,
    goal: &Goal,
    new_ty: &Expr,
    false_proof: &Expr,
) -> bool {
    if !is_false_prop(new_ty) {
        return false;
    }
    let false_elim = Name::from_string("False.elim");
    if state.env.get_const(&false_elim).is_none() {
        return false;
    }
    // `False.elim.{u} : {C : Sort u} → False → C`; the target need not be a
    // proposition (`def f (h : QQ n) : Nat := by simp only [lemN] at h`).
    let target = state.metas.instantiate(&goal.target);
    let Some(level) = get_sort_level(state, goal, &target) else {
        return false;
    };
    let proof = Expr::apps(
        Expr::const_(false_elim, vec![level]),
        [target, false_proof.clone()],
    );
    state.close_goal(goal, proof).is_ok()
}

/// Close the current goal from `proof` when its type is `False` — the
/// `using` term of `simpa … using e`, after its type was simplified.
///
/// Lean's `simpa` notes `e` as a hypothesis and runs `simpGoal` on it
/// (`Lean/Elab/Tactic/Simpa.lean`); when `applySimpResult` closes the goal
/// because the hypothesis became `False`, `simpGoal` returns `none` and
/// `simpa` is done — there is no closing `exact`. Clean went on to `exact`
/// the transported term and failed "False vs 1 = 2" (measured 2026-09-20:
/// `simpa only [nQ] using h` with `nQ : ¬ QQ n`, `h : QQ 1`, which pinned
/// v4.30.0-rc2 accepts).
///
/// ENSURES: `true` iff the goal was closed by the checked `close_goal`; on
///   `false` the proof state is unchanged.
pub(crate) fn close_goal_by_proof_of_false(state: &mut ProofState, proof: &Expr) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let Ok(ty) = state.infer_type(&goal, proof) else {
        return false;
    };
    // The transported term is `Eq.subst (motive := fun x => x) … e`, whose
    // inferred type is the motive APPLIED to the simplified statement.
    let ty = crate::tactic::op_projection::head_beta(&state.metas.instantiate(&ty));
    close_goal_by_false_hypothesis(state, &goal, &ty, proof)
}

/// Whether a `simp … at h` step closed the goal it ran on, given the number
/// of open goals before it: replacing a hypothesis swaps the front goal for a
/// new one, so the count only drops when the goal was closed. A caller that
/// visits several locations must stop then, as Lean's `simpGoal` does —
/// the next location would otherwise be looked up in an unrelated goal.
pub(crate) fn simp_at_closed_goal(state: &ProofState, goals_before: usize) -> bool {
    state.goals.len() < goals_before
}
