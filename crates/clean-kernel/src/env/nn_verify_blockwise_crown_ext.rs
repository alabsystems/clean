// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C006 Extended: LayerNorm Zonotope + Complexity — MASQUERADE RETIRED
//!
//! **Status:** This file is the orchestrator for the C006-extended LayerNorm /
//! complexity surface (T20-T22, T60-T61). The T20/T21/T22 registrations live in
//! their own modules to stay under the 500-line cap. As of the #3509 Branch B
//! waves, NONE of T20-T22 is an axiom any longer.
//!
//! **T20 (`zonotope_reset`) is RETIRED** (#3509 Branch B): its faithful
//! LayerNorm-transfer restatement + the `layernorm_zono` / `zonotope_output`
//! carriers live in `nn_verify_blockwise_crown_ext_t20.rs`. `zonotope_output` is
//! now the interval hull of the faithful affine transfer `x ↦ γ ⊙ x + β`
//! (genuinely consuming γ, β); the former axiom is replaced by two kernel-checked
//! `Declaration::Theorem`s pinning the LN-output box per component.
//!
//! **T21 (`zonotope_width_preserved`) is RETIRED** (#3509 Branch B, T21 half):
//! the false unconditional width-preservation axiom is replaced by a
//! kernel-checked GAIN-BOUND `Declaration::Theorem`
//! (`(∀ i, |γ i| ≤ 1) → l1(width(zonotope_output …)) ≤ l1(width(to_ibp …))`),
//! proven over the faithful `to_ibp ∘ layernorm_zono` carriers in
//! `nn_verify_blockwise_crown_ext_t21.rs`. The old unconditional statement was
//! FALSE under faithful LN gain (`|γ_i| > 1` scales the radius / exceeds the
//! input width), so it was RESTATED under the genuine gain bound, not proved.
//! Domain TCB 5 → 4.
//!
//! T22 `zonotope_generators_reset` and its carrier `generators_after_ln` live in
//! `nn_verify_blockwise_crown_ext_t22.rs` (#3495/#3590 Branch B — also retired
//! via a faithful matrix restatement). NO `sorry`, NO `add_decl_structural`.
//!
//! See `nn_verify_blockwise_crown.rs` for full C006 status.
//! See: designs/2026-04-19-demasquerade-cxxx-pattern.md
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ---
//!
//! Extended block-wise CROWN theorems (T20-T22, T60-T61, Phase 3).
//!
//! Builds on `nn_verify_blockwise_crown.rs` (C006 base) with additional
//! LayerNorm zonotope reset theorems and complexity analysis.
//!
//! ## LayerNorm Zonotope Reset (T20-T22)
//!
//! - **T20: `layernorm_zonotope_reset`** — After LayerNorm, the zonotope
//!   correlation structure is destroyed, resetting to interval abstraction.
//! - **T21: `layernorm_zonotope_width_preserved`** — The width of the
//!   zonotope is preserved through LayerNorm (output IB has same width).
//! - **T22: `layernorm_zonotope_generators_reset`** — Number of generators
//!   resets to n (dimension) after LayerNorm, from any k.
//!
//! ## Block-wise CROWN Complexity (T60-T61)
//!
//! - **T60: `blockwise_crown_equiv`** — Block-wise CROWN produces the
//!   same bounds as full (monolithic) CROWN (C006 equivalence, restated
//!   with complexity annotations).
//! - **T61: `blockwise_complexity`** — Block-wise CROWN has complexity
//!   O(sum_i n_i^2) vs O(N^2) for monolithic, where N = sum n_i.
//!
//! T60 upgraded from axiom to theorem (#3309): delegates to
//! `blockwise_equals_monolithic`. Remaining declarations are axioms.
//!
//! Part of #3153.

use crate::env::{EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize extended block-wise CROWN declarations (T20-T22, T60-T61).
    ///
    /// Depends on:
    /// - `init_nn_verify_blockwise_crown()` for C006 base
    /// - `init_nn_verify_foundation_types()` for width, l1_norm
    /// - `init_nn_verify_zonotope()` for Zonotope, to_ibp
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_blockwise_crown_ext(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.LayerNorm.zonotope_reset"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;
        self.init_nn_verify_foundation_types()?;
        self.init_nn_verify_blockwise_crown()?;

        // T20 + the faithful `layernorm_zono` / `zonotope_output` carriers live
        // in `nn_verify_blockwise_crown_ext_t20.rs` (#3509 Branch B FAITHFUL
        // restatement — the former axiom is RETIRED). The split mirrors the T22
        // split, keeps this file under the 500-line cap, and localises the
        // MASQUERADE history. `register_t20_layernorm_zonotope_reset_ext`
        // registers `zonotope_output` (which T21 below still references).
        self.register_t20_layernorm_zonotope_reset_ext()?;
        // T21 + L0/L2 + its faithful GAIN-BOUND proof live in
        // `nn_verify_blockwise_crown_ext_t21.rs` (#3509 Branch B, T21 half —
        // the former axiom is RETIRED). The split mirrors the T20/T22 splits
        // and keeps this file under the 500-line cap.
        self.register_t21_layernorm_width_preserved()?;
        // T22 + `generators_after_ln` live in
        // `nn_verify_blockwise_crown_ext_t22.rs` (#3495 MASQUERADE
        // remediation) — the split keeps this file under the 500-line cap
        // and localises the Nat.rec induction proof.
        self.register_t22_layernorm_generators_reset_ext()?;
        // T60/T61 + supporting defs in nn_verify_blockwise_crown_ext_defs.rs
        self.register_blockwise_crown_cost_ext()?;
        self.register_block_total_dim_ext()?;
        self.register_t60_blockwise_crown_equiv_ext()?;
        self.register_t61_blockwise_complexity_ext()?;
        // #3494 Phase 2 — faithful Block.monolithic_crown carrier + a
        // companion theorem over it. The old `Block.monolithic_crown`
        // discards `B` and returns `zero_ib`; `monolithic_crown_faithful`
        // returns `B` at `k=0` and `zero_ib` at `k=succ _`, breaking the
        // MASQUERADE. See nn_verify_blockwise_crown_ext_carriers.rs.
        self.register_monolithic_crown_faithful()?;
        self.register_blockwise_crown_equiv_faithful()?;
        // #3491 Phase 2 — faithful Block.compose carrier, structurally
        // distinct from `monolithic_crown_faithful` because its step case
        // applies the block function `cb m ih` rather than discarding IH.
        self.register_compose_faithful()?;
        self.register_compose_faithful_zero_eq_input()?;
        // #3533 Phase 3 — generic successor-unfold lemma for
        // `compose_faithful`. Strictly stronger than the `k=0`
        // specialisation: together the two theorems specify the carrier
        // by its Nat.rec equations. Proof term is `Eq.refl` on the
        // constructed RHS `cb m (compose_faithful d m cb B)`, which
        // the kernel matches against the LHS via a single iota step on
        // Nat.rec at the `Nat.succ` branch.
        self.register_compose_faithful_succ_unfold()?;
        // #3492 Phase-2 foundation — faithful Block-count carrier
        // `NNVerify.Block.compose_count : Nat -> Nat` whose body
        // structurally uses `Nat.rec` with a step branch that references IH.
        self.register_block_compose_count()?;
        // #3375 constructive helper — genuine Nat.rec induction proof
        // `NNVerify.Block.compose_count_eq_self : forall k, compose_count k = k`.
        // Step case uses `congrArg Nat.succ ih`, consuming the IH. This is
        // the smallest tractable incremental constructive theorem over the
        // faithful C006 carrier surface: it would FAIL to type-check if the
        // carrier's step branch discarded its IH, so it locks in the
        // carrier-distinguishing shape. Does NOT retire a C006 axiom, but
        // unblocks future faithful `Block.compose` demasquerade work.
        self.register_compose_count_eq_self()?;
        Ok(())
    }
}
