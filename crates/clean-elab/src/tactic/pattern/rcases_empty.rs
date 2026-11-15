// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The empty tuple pattern `⟨⟩` — Lean 4.8's `RCasesPatt.tuple _ []`, which
//! is also what `rcases e` with no `with` clause destructures by
//! (`Lean/Elab/Tactic/RCases.lean`, `evalRCases`: `none => pure
//! (RCasesPatt.tuple tk [])`).
//!
//! `rcasesCore` sends it down its main path: the hypothesis's type is put in
//! weak head normal form and, when it is an inductive, `processConstructors`
//! pads every constructor's fields with `_` and `MVarId.cases` splits it ONE
//! level — `rcases h` on `h : a ∨ b` leaves two goals, on `h : False` none.
//! Any other type is refused (`rcases tactic failed: … is not an inductive
//! datatype`). A single-constructor index-free inductive never reaches here:
//! `destruct_hypothesis` already destructures it with every field `_`.

use clean_kernel::Name;
use clean_parser::SurfaceName;

use super::super::proof_manipulation::cases;
use super::super::{ProofState, TacticError, TacticResult};
use super::RIntroPattern;

/// Split `hyp_name`, whose type's head is `inductive` (after `whnf`), one
/// level with every field `_`, as Lean's `rcasesCore` does for `⟨⟩`.
///
/// SOUNDNESS: the goal is only transformed by the kernel-checked `cases`
/// (directly, or through the `|` engine with `_` for every constructor); a
/// type that is not an inductive is refused, never left as a silent no-op.
/// An indexed family Clean's `cases` cannot eliminate keeps the pre-existing
/// no-op (the state is restored), which adds no proof step.
pub(super) fn split_one_level(
    state: &mut ProofState,
    hyp_name: &SurfaceName,
    inductive: Option<&Name>,
) -> TacticResult {
    let shape = inductive
        .and_then(|name| state.env.get_inductive(name))
        .map(|ind| (ind.constructor_names.len(), ind.num_indices));
    let Some((constructors, indices)) = shape else {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: format!(
                "rcases tactic failed: '{hyp_name}' is not an inductive datatype, so the empty \
                 pattern `⟨⟩` (the pattern of `rcases` without `with`) cannot split it"
            ),
        });
    };
    if indices == 0 {
        let alternatives = vec![RIntroPattern::Wildcard; constructors];
        return super::rintro::split_or_hypothesis(state, hyp_name, &alternatives);
    }
    // An indexed family (`Eq`, `List.Mem`, …): Lean's `MVarId.cases`, whose
    // index unification is what `cases h` runs.
    //
    // DIVERGENCE (refusal-preserving fallback): Clean's `cases` now unifies
    // an equation's sides the way Lean's `unifyEqs?` does, injection included
    // (G82, `crate::tactic::cases_unify_eqs`), but still refuses the steps it
    // does not implement (`acyclic`; a hypothesis that another one mentions)
    // and every equation Lean reports "dependent elimination failed" on.
    // There the hypothesis is left in place, as `⟨⟩` always left a
    // non-splittable hypothesis before (`rintro ⟨⟩ ⟨⟩ ⟨⟩` on
    // `Function.Injective (@PartialOrder.toPreorder α)`,
    // `Mathlib/Order/Basic.lean`, was the measured case); the state is
    // restored first, so a half-run `cases` leaves nothing behind.
    let saved = state.clone();
    if cases(state, hyp_name).is_err() {
        *state = saved;
    }
    Ok(())
}
