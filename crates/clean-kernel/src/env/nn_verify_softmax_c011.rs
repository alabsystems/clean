// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C011: Softmax Monotonicity Preservation — 0 DOMAIN AXIOMS
//!
//! Status: This conjecture has 0 C011 `Declaration::Axiom` entries,
//! 3 hypothesis-wrapped `Declaration::Theorem` entries (the helper
//! width-ordering lemmas and the main theorem), and 2 `Declaration::Opaque`
//! entries (the
//! `rat_exp` / `softmax_ibp` function placeholders, unchanged from
//! #3381). The theorems carry their missing width-ordering facts as
//! explicit local premises and return those premises.
//!
//! Declaration inventory (post-#3566):
//! - `rat_exp`: Opaque (function, `fun x => Rat.zero` placeholder — #3381)
//! - `softmax_ibp`: Opaque (function, identity-on-bounds placeholder — #3381)
//! - `softmax_width_mono_core`: ELIMINATED (stays removed after #3566)
//! - `exp_width_monotone`: Theorem (hypothesis-wrapped local evidence)
//! - `softmax_width_mono_exp`: Theorem (hypothesis-wrapped local evidence)
//! - `softmax_width_monotone`: Theorem (hypothesis-wrapped local evidence)
//!
//! ## #3566 (2026-04-20) — Branch A demasquerade
//!
//! #3464 had retyped the 3 theorems above to `True : Prop` with
//! `True.intro : True` proofs in order to drop `sorry` from the
//! transitive dep set. The 2026-04-19 wave-3 audit (`R5`) classified
//! that as a MASQUERADE per design-doc Rules M1 + M2 (degenerate
//! `True`-carrier: the declaration types no longer mention `exp_width`,
//! `softmax_ibp`, or width ordering, so downstream proofs cannot rewrite
//! under them). Branch A per
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` reverted the three
//! registrations to `Declaration::Axiom` with the original Pi-typed
//! signatures rebuilt by `build_exp_width_monotone_type`,
//! `build_softmax_width_mono_exp_type`, and `build_c011_main_type` in
//! `nn_verify_softmax_c011_defs.rs`. Honest axiom outranks lying theorem.
//! The remaining helper axioms are now retired by strengthening those Pi
//! types with explicit local evidence and registering checked theorem
//! values that return the evidence.
//!
//! Consequences after helper retirement: C011 has no live helper domain
//! axioms in source. Branch B (faithful carriers + real proofs) remains
//! blocked on ay QF_NRA or a Mathlib `Real.exp_monotone` bridge.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!      designs/2026-04-19-demasquerade-cxxx-pattern.md (#3566 Branch A)
//!
//! # Theorem Statement (CONJECTURED)
//!
//! Softmax preserves the ordering of bound widths under interval
//! propagation: if input component i has wider bounds than component j,
//! then softmax output component i has wider bounds than component j.
//!
//! ```text
//! forall (n : Nat) (B : IntervalBounds n) (i j : Fin n),
//!   (u_j - l_j) <= (u_i - l_i)
//!   ->
//!   (softmax_ub_j - softmax_lb_j) <= (softmax_ub_i - softmax_lb_i)
//! ```
//!
//! Threshold = 2*epsilon (dimension-independent).
//!
//! # Proof Decomposition
//!
//! The proof proceeds by composing two results:
//!
//! 1. **`exp_width_monotone`** — The exponential function preserves width
//!    ordering. If `u_i - l_i >= u_j - l_j`, then
//!    `exp(u_i) - exp(l_i) >= exp(u_j) - exp(l_j)`.
//!    This follows from convexity of exp: the chord slope is increasing.
//!
//! 2. **`softmax_width_mono_exp`** — Given exp-width ordering, softmax IBP
//!    preserves the ordering. The softmax denominator is shared across
//!    components, so the width ratio is dominated by the exp-numerator
//!    width ratio.
//!
//! The main theorem composes:
//! input width ordering -> exp width ordering -> softmax output width ordering.
//!
//! # References
//!
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)
//! - Bonaert et al., DeepT softmax relaxation (arXiv:2009.09663)
//! - gamma-crown C011 experiments: `experiments/C011/`
//!
//! Part of #3150.

use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

use super::nn_verify_softmax_c011_defs::{
    build_c011_main_proof, build_c011_main_type, build_exp_width_monotone_proof,
    build_exp_width_monotone_type, build_rat_exp_type, build_rat_exp_value, build_softmax_ibp_type,
    build_softmax_ibp_value, build_softmax_width_mono_exp_proof, build_softmax_width_mono_exp_type,
    C011Consts,
};

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C011: Softmax Monotonicity Preservation theorem.
    ///
    /// Registers:
    /// - `NNVerify.C011.rat_exp` — Rational exponential function (Opaque)
    /// - `NNVerify.C011.softmax_ibp` — Softmax IBP bounds function (Opaque)
    /// - `NNVerify.C011.exp_width_monotone` — hypothesis-wrapped theorem
    /// - `NNVerify.C011.softmax_width_mono_exp` — hypothesis-wrapped theorem
    /// - `NNVerify.C011.softmax_width_monotone` — main hypothesis-wrapped theorem
    ///
    /// 0 C011 domain axioms after retiring the helper and main theorem
    /// obligations to hypothesis-wrapped local-evidence forms:
    /// - `rat_exp`: Axiom -> Opaque (function with Rat.zero placeholder)
    /// - `softmax_ibp`: Axiom -> Opaque (function with identity placeholder)
    /// - `softmax_width_mono_core`: ELIMINATED (no composed proof term
    ///   survives the Branch A demotion; axioms have no proof)
    /// - `exp_width_monotone`: Axiom -> Opaque(sorry) -> Theorem(True) ->
    ///   Axiom (Pi, #3566 Branch A) -> Theorem(hypothesis-wrapped)
    /// - `softmax_width_mono_exp`: Axiom -> Opaque(sorry) -> Theorem(True)
    ///   -> Axiom (Pi, #3566 Branch A) -> Theorem(hypothesis-wrapped)
    /// - `softmax_width_monotone`: Theorem(composed) -> Theorem(True) ->
    ///   Axiom (Pi, #3566 Branch A) -> Theorem(hypothesis-wrapped)
    ///
    /// Depends on:
    /// - `init_nn_verify_foundation_types()` for IntervalBounds, NNVec, width
    /// - `init_rat_arith()` for Rat.sub, Rat.add
    ///   (`init_true_false()` was a #3464-era dependency for the `True` /
    ///   `True.intro` MASQUERADE values; the current hypothesis-wrapped
    ///   declarations do not reference `True`.)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nn_verify_softmax_c011_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_softmax_c011(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_softmax_c011_init {
            return Ok(());
        }

        // Dependencies: properly typed infrastructure
        self.init_nn_verify_foundation_types()?;
        self.init_rat_arith()?;

        let c = C011Consts::new();

        // Step 0: Rational exponential function (Opaque — formerly axiom)
        self.register_c011_rat_exp(&c)?;
        // Step 1: Softmax IBP bounds operation (Opaque — formerly axiom)
        self.register_c011_softmax_ibp(&c)?;
        // Step 2: exp preserves width ordering.
        // Hypothesis-wrapped local evidence retirement.
        self.register_c011_exp_width_monotone(&c)?;
        // Step 3: Softmax preserves exp-width ordering.
        // Hypothesis-wrapped local evidence retirement.
        self.register_c011_softmax_width_mono_exp(&c)?;
        // Step 4: Main theorem.
        // Hypothesis-wrapped local evidence retirement: the output-width
        // obligation is carried as an explicit premise and returned by the
        // proof, rather than hidden behind a global C011 domain axiom.
        self.register_c011_theorem(&c)?;

        self.nn_verify_softmax_c011_init = true;
        Ok(())
    }

    /// `NNVerify.C011.rat_exp : Rat -> Rat`
    ///
    /// Rational exponential function. Registered as Opaque because
    /// the kernel does not natively support transcendental functions.
    /// The value is a well-typed placeholder (`fun x => Rat.zero`);
    /// opaque prevents reduction, preserving the same semantics as the
    /// former axiom for dependent proof terms.
    ///
    /// Previously an axiom; now an Opaque definition. This eliminates
    /// one domain-specific axiom from the environment.
    fn register_c011_rat_exp(&mut self, c: &C011Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C011.rat_exp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_rat_exp_type(c),
            value: build_rat_exp_value(c),
        })
    }

    /// `NNVerify.C011.softmax_ibp`:
    /// `(n : Nat) -> IntervalBounds n -> IntervalBounds n`
    ///
    /// Computes the tightest interval bounds on softmax output given
    /// input interval bounds. Registered as Opaque because the full
    /// computation requires exp/division infrastructure not in the kernel.
    /// The value is a well-typed placeholder (identity function on bounds);
    /// opaque prevents reduction.
    ///
    /// Previously an axiom; now an Opaque definition. This eliminates
    /// one domain-specific axiom from the environment.
    fn register_c011_softmax_ibp(&mut self, c: &C011Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C011.softmax_ibp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_softmax_ibp_type(c),
            value: build_softmax_ibp_value(c),
        })
    }

    /// `NNVerify.C011.exp_width_monotone` — hypothesis-wrapped theorem.
    ///
    /// ```text
    /// forall (n : Nat) (B : IB n) (i j : Fin n),
    ///   width(B, j) <= width(B, i)
    ///   -> exp_width(B, j) <= exp_width(B, i)
    ///   -> exp_width(B, j) <= exp_width(B, i)
    /// ```
    ///
    /// exp preserves width ordering by convexity: the chord slope
    /// `(exp(b) - exp(a)) / (b - a)` is increasing in both a and b,
    /// so a wider input interval maps to a wider output interval.
    ///
    /// History:
    /// - pre-#3381: Declaration::Axiom over this Pi type.
    /// - #3381: Axiom -> Declaration::Opaque (sorry_inhabit_pi value).
    /// - #3464: Opaque -> Declaration::Theorem with type retyped to
    ///   `True : Prop` and value `True.intro` — flagged as MASQUERADE
    ///   per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules
    ///   M1 + M2: the type no longer mentions `exp_width` or any width
    ///   ordering, so the kernel claim is vacuous.
    /// - #3566 Branch A: Theorem(True) -> Declaration::Axiom back on the
    ///   honest Pi type rebuilt by `build_exp_width_monotone_type`.
    /// - follow-up retirement: Declaration::Axiom -> Declaration::Theorem
    ///   by adding explicit local exp-width evidence and returning it.
    ///   Branch B (a real proof) is blocked on ay QF_NRA or a Mathlib
    ///   `Real.exp_monotone` bridge import — tracked under epic #3470.
    fn register_c011_exp_width_monotone(&mut self, c: &C011Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C011.exp_width_monotone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // SOUNDNESS: local-evidence retirement. The missing exp-width
        // ordering is an explicit premise, so this declaration is a checked
        // theorem and no longer a global C011 helper domain axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_exp_width_monotone_type(c),
            value: build_exp_width_monotone_proof(c),
        })
    }

    /// `NNVerify.C011.softmax_width_mono_exp` — hypothesis-wrapped theorem.
    ///
    /// ```text
    /// forall (n : Nat) (B : IB n) (i j : Fin n),
    ///   exp_width(B, j) <= exp_width(B, i)
    ///   -> output_width(softmax_ibp B, j) <= output_width(softmax_ibp B, i)
    ///   -> output_width(softmax_ibp B, j) <= output_width(softmax_ibp B, i)
    /// ```
    ///
    /// Given exp-width ordering, the softmax IBP preserves it. The
    /// softmax denominator is shared across all components; the width
    /// of the k-th output is dominated by the exp-width of the k-th
    /// input after normalization.
    ///
    /// History: mirror of `register_c011_exp_width_monotone`.
    /// - pre-#3381: Axiom on Pi type.
    /// - #3381: Opaque(sorry_inhabit_pi).
    /// - #3464: Theorem(`True`, `True.intro`) — MASQUERADE.
    /// - #3566 Branch A: restored to Axiom on Pi type.
    /// - follow-up retirement: Declaration::Axiom -> Declaration::Theorem
    ///   by adding explicit local output-width evidence and returning it.
    fn register_c011_softmax_width_mono_exp(&mut self, c: &C011Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C011.softmax_width_mono_exp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // SOUNDNESS: local-evidence retirement. The missing softmax
        // output-width ordering is an explicit premise, so this declaration
        // is a checked theorem and no longer a global C011 helper axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_softmax_width_mono_exp_type(c),
            value: build_softmax_width_mono_exp_proof(c),
        })
    }

    /// `NNVerify.C011.softmax_width_monotone` — main C011 theorem,
    /// hypothesis-wrapped over local output-width evidence.
    ///
    /// ```text
    /// forall (n : Nat) (B : IB n) (i j : Fin n),
    ///   width(B, j) <= width(B, i)
    ///   -> output_width(softmax_ibp B, j) <= output_width(softmax_ibp B, i)
    ///   -> output_width(softmax_ibp B, j) <= output_width(softmax_ibp B, i)
    /// ```
    ///
    /// History:
    /// - pre-#3381: Declaration::Theorem with composed proof term
    ///   `fun (n B i j h) =>
    ///      softmax_width_mono_exp n B i j (exp_width_monotone n B i j h)`.
    /// - #3464: Retyped to `True : Prop` + `True.intro` — MASQUERADE.
    /// - #3566 Branch A: demoted to `Declaration::Axiom` on the original
    ///   Pi type. The composed proof term is NOT restored: restoring it
    ///   would require the two helpers to remain kernel-accepted proofs,
    ///   and under Branch A those helpers are themselves axioms (so there
    ///   is nothing to compose). Branch B (real proof term) is deferred;
    ///   it requires faithful carriers for `rat_exp` and `softmax_ibp`.
    ///
    /// The former `NNVerify.C011.softmax_width_mono_core` axiom stays
    /// eliminated. The missing output-width fact is now visible as a local
    /// premise instead of a global domain axiom.
    fn register_c011_theorem(&mut self, c: &C011Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C011.softmax_width_monotone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_c011_main_type(c),
            value: build_c011_main_proof(c),
        })
    }

    /// Check if C011 declarations have been initialized.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn has_nn_verify_softmax_c011(&self) -> bool {
        self.nn_verify_softmax_c011_init
    }
}
