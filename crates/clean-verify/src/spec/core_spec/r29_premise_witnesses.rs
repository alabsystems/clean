// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Witnesses for the two predicates the premise-satisfiability ratchet flags.**
//!
//! `crates/clean-verify/tests/premise_witness_gate.rs` is RED at HEAD on `TmC`
//! and `r29_ctxOK` — both assumed in hypothesis position with nothing in the
//! spec concluding them, and neither in the baseline's `unwitnessed` list. The
//! gate names two ways out: SUPPLY a witness, or record the premise as
//! genuinely open with a justification.
//!
//! The second is a judgement about the intent of the r29 rung and belongs to
//! its owner. **The first is just work**, and it is attempted here.
//!
//! # Why this is worth more than turning a gate green
//!
//! `r29_sn` — the strong-normalization capstone CLAUDE.md advertises — reads
//! `TmC G e T -> whnf_acc e`. If nothing inhabits `TmC`, that capstone is
//! conditional on a premise nothing produces, which is the same vacuity
//! question the `CandModel` telescope has open and the same shape as the
//! loop-(i) precedent. A closed `TmC` derivation settles it in the good
//! direction.
//!
//! # What each costs
//!
//! `TmC.var : forall G i, TmC G (bvar i) (G i)` takes NO premises, so the
//! judgment is trivially inhabited and the witness is one line. That is the
//! whole answer for `TmC`, and it means the capstone was never at risk — only
//! unrecorded.
//!
//! `r29_ctxOK G := forall qi, InertTy (G qi)` needs a context whose every slot
//! is inert, and `InertTy`'s base case `konst` demands a constant that is
//! δ-free AND recursor-free in the fixed `the_red_env`. Every existing use
//! CARRIES those as hypotheses (`whnfAcc_const`, `no_whnf_step_const`,
//! `wFresh_rec`); discharging them concretely asks `defval_for` / `recmeta_for`
//! to COMPUTE to `none` over the reflected foundation core, which is a large
//! generated environment. Whether that reduces at acceptable cost is the open
//! question this module measures, and it is the reason the two witnesses are
//! registered SEPARATELY: if the context one is too expensive, the `TmC` one
//! still lands and still settles the capstone.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// `TmC` is INHABITED. One line, because `TmC.var` has no premises.
    ///
    /// Read against `r29_sn : TmC G e T -> whnf_acc e`: the capstone's premise
    /// has a closed inhabitant, so the theorem is not vacuous.
    pub(super) fn r29_tmc_witness_src() -> String {
        let ctx = "(fun (_qi : Nat) => KExpr.sort Level.zero)";
        format!(
            "def r29_tmC_witness : TmC {ctx} (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) := \
             TmC.var {ctx} Nat.zero"
        )
    }

    /// `InertTy` at a constant the reflected environment does not define.
    ///
    /// `Name.anonymous` is not an interned key: `kernel_core_red_env` interns
    /// every real name as `Name.str Name.anonymous <unary tag>`, so the bare
    /// root is absent by construction. Both premises are then `Eq.refl` IF the
    /// lookups reduce.
    pub(super) fn r29_inertty_witness_src() -> String {
        "def r29_inertTy_witness : \
         InertTy (KExpr.const Name.anonymous (@ListType.nil Level)) := \
         InertTy.konst Name.anonymous (@ListType.nil Level) \
         (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)) \
         (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))"
            .to_string()
    }

    /// `r29_ctxOK` at the constant context built from that inert type.
    pub(super) fn r29_ctxok_witness_src() -> String {
        let ctx = "(fun (_qi : Nat) => KExpr.const Name.anonymous (@ListType.nil Level))";
        format!(
            "def r29_ctxOK_witness : r29_ctxOK {ctx} := \
             fun (qi : Nat) => r29_inertTy_witness"
        )
    }

    pub(super) fn r29_premise_witness_sources() -> Vec<(String, String)> {
        vec![
            ("r29_tmC_witness".to_string(), Self::r29_tmc_witness_src()),
            (
                "r29_inertTy_witness".to_string(),
                Self::r29_inertty_witness_src(),
            ),
            (
                "r29_ctxOK_witness".to_string(),
                Self::r29_ctxok_witness_src(),
            ),
        ]
    }
    /// Registered after `add_candmodel_construct_r29`, which mints `TmC` and
    /// `r29_ctxOK`; `InertTy` comes from r28 just before it and `the_red_env`
    /// far earlier.
    pub(super) fn add_r29_premise_witnesses(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::r29_premise_witness_sources() {
            self.add_recursive_def(&src, "r29 premise witnesses")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "r29_premise_witnesses_tests.rs"]
mod tests;
