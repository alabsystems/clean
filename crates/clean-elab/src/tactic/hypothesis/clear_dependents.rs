// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `MVarId.clear` dependency refusals (`Lean/Meta/Tactic/Clear.lean`).
//!
//! Lean walks the local context in order and refuses with "variable 'x'
//! depends on 'h'" at the first local other than `h` whose type or value
//! mentions `h`, then with "target depends on 'h'" when the goal does; only
//! then is `h` removed. Pinned Lean 4.8.0 (2026-10-16):
//!
//! ```text
//! theorem c1 (a : Nat) (h : a = 1) (hp : h = h) : True := by clear h
//!   -- tactic 'clear' failed, variable 'hp' depends on 'h'
//! theorem c2 (a : Nat) (h : a = 1) : h = h := by clear h
//!   -- tactic 'clear' failed, target depends on 'h'
//! ```
//!
//! Mathlib's `apply_fun … at h` clears `h` the same way before it `note`s the
//! new hypothesis (`Mathlib/Tactic/ApplyFun.lean`, `applyFunHyp`), so it
//! refuses with the same messages.

use clean_kernel::Expr;

use crate::tactic::{Goal, ProofState, TacticError};

/// Refuse to clear `goal.local_ctx[idx]` when a LATER local or the target
/// mentions it, with Lean's message for the first such dependent.
///
/// REQUIRES: `idx < goal.local_ctx.len()`.
/// ENSURES: `Ok(())` exactly when nothing after the local, and not the
///   target, mentions its fvar (metavariables instantiated first).
pub(crate) fn refuse_if_depended_on(
    state: &ProofState,
    goal: &Goal,
    idx: usize,
) -> Result<(), TacticError> {
    let cleared = &goal.local_ctx[idx];
    let mentions =
        |e: &Expr| super::collect_fvars(&state.metas.instantiate(e)).contains(&cleared.fvar);
    if let Some(dependent) = goal
        .local_ctx
        .iter()
        .skip(idx + 1)
        .find(|decl| mentions(&decl.ty) || decl.value.as_ref().is_some_and(mentions))
    {
        return Err(clear_refusal(format!(
            "variable '{}' depends on '{}'",
            dependent.name, cleared.name
        )));
    }
    if mentions(&goal.target) {
        return Err(clear_refusal(format!(
            "target depends on '{}'",
            cleared.name
        )));
    }
    Ok(())
}

fn clear_refusal(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "clear".into(),
        detail,
    }
}
