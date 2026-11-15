// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic sequence evaluation.
//!
//! Compound tactic dispatch migrated to registry-based handlers in
//! `builtins_compound.rs` (Wave 5) and `builtins_phase3d_elab.rs` (Wave 6).
//! This file retains only `eval_tactic_seq`, which is used by `elab_by_tactic`
//! and the `TacticEval` implementation on `ElabCtx`.

use super::ElabCtx;
use crate::tactic::ProofState;
use crate::ElabError;
use clean_parser::SurfaceTactic;

impl<'a> ElabCtx<'a> {
    /// Run a sequence of tactics.
    pub(super) fn eval_tactic_seq(
        &mut self,
        ps: &mut ProofState,
        tacs: &[SurfaceTactic],
    ) -> Result<(), ElabError> {
        let saved = self.classical_tactic_scope;
        let result = tacs.iter().try_for_each(|t| {
            self.enter_classical_if_opener(ps, t);
            self.eval_tactic(ps, t)
        });
        self.leave_classical_scope(ps, saved);
        result
    }

    /// A bare `classical` opens a classical scope for the REST of its tactic
    /// sequence (Lean: `"classical" ppDedent(tacticSeq)`, which adds
    /// `Classical.propDecidable` as a local instance while that sequence
    /// runs). Clean's `classical` handler was a structural no-op, so a later
    /// `exact`/`simp` that needed `Decidable (p x)` failed to synthesize it
    /// (`Subtype.surjective_restrict`, measured 2026-09-12).
    ///
    /// The depth is RE-PUBLISHED to the `ProofState` here, not only at the
    /// block's entry: `set_instance_visibility` runs once before any tactic
    /// does (`elab_tactic.rs`), so a `classical` opened MID-block would
    /// otherwise never reach a tactic-side instance query
    /// (`InstanceVisibility::classical_scope`).
    pub(super) fn enter_classical_if_opener(&mut self, ps: &mut ProofState, t: &SurfaceTactic) {
        if matches!(t, SurfaceTactic::Named { name, args, .. } if name == "classical" && args.is_empty())
        {
            self.classical_tactic_scope += 1;
            self.instance_cache.clear();
            ps.set_instance_visibility(self.instance_visibility());
        }
    }

    /// Restore the classical depth a sequence started with, and re-publish it.
    pub(super) fn leave_classical_scope(&mut self, ps: &mut ProofState, saved: u32) {
        if self.classical_tactic_scope != saved {
            self.classical_tactic_scope = saved;
            self.instance_cache.clear();
            ps.set_instance_visibility(self.instance_visibility());
        }
    }
}
