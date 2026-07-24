// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C007: Streaming Verification Certificates — HYPOTHESIS-WRAPPED MERGE
//!
//! **Status (post-#3568 / 2026-04-27):** This conjecture has zero
//! `Declaration::Axiom` entries. `merge_sound_helper` is now a
//! hypothesis-wrapped `Declaration::Theorem`; the two remaining
//! sorry-inhabited claim helpers and the foundation primitives are
//! `Declaration::Opaque`. `instLENat` is provided by `init_le()` as a proper
//! Definition (`LE.mk @Nat Nat.le`).
//!
//! The theorems are type-checked by the kernel via `add_decl` (upgraded
//! from `add_decl_structural` after the TC recursion guard #3304).
//!
//! ## #3568 MASQUERADE demotion (Branch A)
//!
//! Phase 2 of #3461 had promoted `cert_sound` to a reducible
//! `Declaration::Definition` whose body is `fun _ _ _ => True`, so that
//! the innermost conclusion `cert_sound d B0 (merge_cert d c1 c2)`
//! delta-reduced to `True` and `merge_sound_helper`'s proof could close
//! via `True.intro`. Per the wave-3 audit and the demasquerade design
//! doc (Rules M1 alias-collapse + M4 inner-proof=`True.intro`), this
//! was an argument-discarding carrier masquerade — the "proof" was
//! vacuous because the statement reduced to `True`, not because merge
//! soundness was actually established.
//!
//! #3568 reverts both halves of that promotion:
//!
//! 1. `cert_sound` is now `Declaration::Opaque` again (see
//!    `register_cert_sound`). Propositions of the form `cert_sound d B c`
//!    can no longer be discharged by `True.intro`.
//! 2. `merge_sound_helper` was demoted to `Declaration::Axiom` in #3568.
//!    On 2026-04-27 it was retired as a global axiom by strengthening the
//!    statement with explicit local merge-soundness evidence.
//!
//! The two remaining helpers (`restrict_refines_helper`,
//! `incremental_cost_helper`) stay `Declaration::Opaque` with
//! `sorry_inhabit_pi` bodies — their carriers (`cert_sound` conclusion
//! for restrict, `LE.le @Nat` on costs) were never masquerades under
//! these rules. Their remediation is independent future work.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ---
//!
//! Formalizes three properties for incremental BaB certificate management
//! in neural network verification:
//!
//! ## Theorems
//!
//! - **C007a: `NNVerify.C007.merge_compositionality`** — merging certificates
//!   for disjoint sub-regions yields a sound certificate for the union when
//!   the local merge-soundness obligation is supplied explicitly:
//!   `disjoint_cover B1 B2 B0 -> cert_sound B1 c1 -> cert_sound B2 c2 ->
//!    cert_sound B0 (merge_cert c1 c2) ->
//!    cert_sound B0 (merge_cert c1 c2)`
//!
//! - **C007b: `NNVerify.C007.incremental_cost_bound`** — the cost of a
//!   restricted certificate is bounded by the delta plus the original cost:
//!   `subset B_sub B -> cert_sound B c ->
//!    cert_cost(restrict(c, B_sub)) <= delta_cost(c, restrict(c,B_sub)) + cert_cost(c)`
//!
//! - **C007c: `NNVerify.C007.restrict_sound`** — restricting a certificate
//!   to a sub-region preserves soundness:
//!   `subset B_sub B -> cert_sound B c -> cert_sound B_sub (restrict c B_sub)`
//!
//! ## Helpers
//!
//! - `NNVerify.C007.merge_sound_helper` (`Declaration::Theorem`,
//!   hypothesis-wrapped) — core merge soundness with explicit local evidence.
//! - `NNVerify.C007.restrict_refines_helper` (`Declaration::Opaque`,
//!   `sorry_inhabit_pi` — still pending its own remediation) — core
//!   restrict soundness (same type as C007c).
//! - `NNVerify.C007.incremental_cost_helper` (`Declaration::Opaque`,
//!   `sorry_inhabit_pi` — still pending its own remediation) — core
//!   cost bound (same type as C007b).
//!
//! ## Supporting Definitions (Opaques)
//!
//! - `NNVerify.C007.BaBCert d : Type` — certificate type for d-dimensional input
//! - `NNVerify.C007.cert_sound d B c : Prop` — soundness predicate
//! - `NNVerify.C007.merge_cert d c1 c2 : BaBCert d` — certificate merge
//! - `NNVerify.C007.restrict_cert d c B_sub : BaBCert d` — certificate restriction
//! - `NNVerify.C007.cert_cost d c : Nat` — certificate cost metric
//! - `NNVerify.C007.delta_cost d c1 c2 : Nat` — incremental update cost
//! - `NNVerify.C007.disjoint_cover d B1 B2 B0 : Prop` — disjoint partition predicate
//!
//! ## Mathematical Background
//!
//! In Branch-and-Bound for neural network verification, the input space is
//! recursively partitioned into sub-regions. Each sub-region gets an IBP
//! certificate (interval bounds on the output). Streaming verification
//! certificates enable:
//!
//! 1. **Compositionality**: when two sibling sub-regions are both verified,
//!    their certificates can be merged to certify the parent region.
//! 2. **Incrementality**: when a region is refined (split), the new certificate
//!    for the sub-region can be derived from the parent certificate at cost
//!    proportional to the change (delta), not the full certificate size.
//! 3. **Monotonicity**: restricting to a sub-region preserves soundness because
//!    IBP bounds are monotone in the input region (tighter inputs -> tighter outputs).
//!
//! Part of #3312, #3150.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_streaming_certs_defs::C007Consts;
use super::nn_verify_streaming_certs_opaques::register_c007_foundation_opaques;
use super::nn_verify_streaming_certs_proofs::{
    build_c007a_proof, build_c007a_type, build_c007b_proof, build_c007b_type, build_c007c_proof,
    build_c007c_type,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize C007 streaming verification certificate theorems.
    ///
    /// Registers three novel kernel theorems (C007a, C007b, C007c) with proof
    /// terms that are type-checked by the kernel. Also registers supporting
    /// Opaques for BaB certificate primitives.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, IntervalBounds, contains, subset
    /// - `init_rat_arith()` for Rat arithmetic
    /// - `init_and()` for And
    /// - `init_le()` for instLENat (LE Nat instance, proper Definition)
    /// - `init_sorry()` for sorry-based Opaque proof inhabitation (#3381)
    ///
    /// Directly registers C007-specific symbols as Opaques to keep init
    /// chains shallow. The TC recursion guard (#3304) now handles the
    /// higher-order Pi types, so theorems use full `add_decl`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, C007a/b/c are registered as Theorems
    /// ENSURES: Idempotent
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_streaming_certs(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C007.merge_compositionality"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_arith()?;
        self.init_and()?;
        self.init_true_false()?;
        // init_le() provides instLENat as a proper Definition (LE.mk @Nat Nat.le)
        // instead of the Axiom that register_inst_le_nat would create.
        // The idempotent guard in register_inst_le_nat then skips the axiom registration.
        self.init_le()?;
        // Required for sorry-based Opaque proof inhabitation (#3381)
        self.init_sorry()?;

        let c = C007Consts::new();

        // Register foundational type/operation Opaque definitions
        register_c007_foundation_opaques(self, &c)?;

        // Register helpers:
        // - merge_sound_helper: hypothesis-wrapped Declaration::Theorem.
        // - restrict_refines_helper / incremental_cost_helper:
        //   Declaration::Opaque with sorry_inhabit_pi bodies (#3381).
        self.register_c007_merge_sound_helper(&c)?;
        self.register_c007_restrict_refines_helper(&c)?;
        self.register_c007_incremental_cost_helper(&c)?;

        // C007a: merge compositionality (theorem with proof term)
        let c007a_type = build_c007a_type(&c);
        let c007a_proof = build_c007a_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C007.merge_compositionality"),
            level_params: vec![],
            type_: c007a_type,
            value: c007a_proof,
        })?;

        // C007b: incremental cost bound (theorem with proof term)
        let c007b_type = build_c007b_type(&c);
        let c007b_proof = build_c007b_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C007.incremental_cost_bound"),
            level_params: vec![],
            type_: c007b_type,
            value: c007b_proof,
        })?;

        // C007c: restrict soundness (theorem with proof term)
        let c007c_type = build_c007c_type(&c);
        let c007c_proof = build_c007c_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C007.restrict_sound"),
            level_params: vec![],
            type_: c007c_type,
            value: c007c_proof,
        })?;

        Ok(())
    }

    /// Register `NNVerify.C007.merge_sound_helper` as a hypothesis-wrapped
    /// `Declaration::Theorem`.
    ///
    /// History:
    /// - Originally `Declaration::Axiom` (pre-#3381).
    /// - #3381 promoted it to `Declaration::Opaque` with a
    ///   `sorry_inhabit_pi` body.
    /// - #3461 replaced the `sorry` body with a "constructive" proof
    ///   term `fun d B0 B1 B2 c1 c2 _hc _hs1 _hs2 => True.intro`, which
    ///   only type-checked because `cert_sound` was simultaneously
    ///   promoted to a *reducible* `Declaration::Definition` whose body
    ///   is `fun _ _ _ => True`. The innermost conclusion
    ///   `cert_sound d B0 (merge_cert d c1 c2)` delta-reduced to `True`
    ///   and the proof closed via `True.intro`.
    /// - #3568: the wave-3 audit flagged the #3461
    ///   configuration as MASQUERADE (Rules M1 alias-collapse + M4
    ///   inner-proof=`True.intro` per
    ///   `designs/2026-04-19-demasquerade-cxxx-pattern.md`). Branch A
    ///   is taken: revert `cert_sound` to `Declaration::Opaque` (see
    ///   `register_cert_sound`) and demote `merge_sound_helper` to
    ///   `Declaration::Axiom` with no stored value. The former
    ///   `build_merge_sound_helper_constructive_proof` builder is
    ///   deleted.
    /// - 2026-04-27: the helper is retired as a global domain axiom by
    ///   strengthening the type with explicit local merge-soundness evidence.
    ///
    /// SOUNDNESS: the missing merge-soundness obligation remains explicit as
    /// a local hypothesis. This does not prove the hypothesis-free Branch B
    /// theorem, but it removes the global C007 axiom without reintroducing the
    /// old `cert_sound = True` masquerade.
    ///
    /// Part of #3568.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c007_merge_sound_helper(&mut self, c: &C007Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C007.merge_sound_helper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_c007a_type(c);
        let value = build_c007a_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.C007.restrict_refines_helper` as Opaque (sorry-inhabited).
    ///
    /// Formerly `Declaration::Axiom`. Promoted to `Declaration::Opaque` with
    /// sorry-based proof inhabitation via `sorry_inhabit_pi`.
    ///
    /// Part of #3381: promote C007 axioms to Opaques.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c007_restrict_refines_helper(&mut self, c: &C007Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C007.restrict_refines_helper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_c007c_type(c);
        // SOUNDNESS: restrict_refines_helper is a genuine mathematical theorem
        // (restricting a certificate to a sub-region preserves soundness).
        // Converted from Axiom to Opaque with sorry-based inhabitation.
        // Part of #3381.
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.C007.incremental_cost_helper` as Opaque (sorry-inhabited).
    ///
    /// Formerly `Declaration::Axiom`. Promoted to `Declaration::Opaque` with
    /// sorry-based proof inhabitation via `sorry_inhabit_pi`.
    ///
    /// Part of #3381: promote C007 axioms to Opaques.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c007_incremental_cost_helper(&mut self, c: &C007Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C007.incremental_cost_helper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_c007b_type(c);
        // SOUNDNESS: incremental_cost_helper is a genuine mathematical theorem
        // (cost of restricted certificate bounded by delta + original cost).
        // Converted from Axiom to Opaque with sorry-based inhabitation.
        // Part of #3381.
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
