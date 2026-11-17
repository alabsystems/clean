// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Ω is not strongly normalizing — and therefore `pi_elim` is FALSE at the
//! type-blind candidate, not merely unproved there.**
//!
//! `candmodel_inhabit_probe.rs` records `pi_elim` as REFUSED and says, rightly,
//! that a refusal is not a refutation: the elaborator declining to find a term
//! is not a proof that none exists. The argument beside it — that Ω refutes the
//! law — is sound and was not kernel-checked. This module checks it.
//!
//! ```text
//! self_app_loop_not_whnf_acc : whnf_step (app d d) (app d d)
//!                                -> whnf_acc (app d d) -> C
//! omega_self_step            : whnf_step (app D D) (app D D)
//! whnf_acc_omega_lam         : whnf_acc D
//! pi_elim_blind_refuted      : (forall f a, whnf_acc f -> whnf_acc a
//!                                -> whnf_acc (app f a)) -> C
//! ```
//!
//! The first is general and is the whole content: a term that steps to itself
//! cannot be accessible, by one `whnf_acc.rec` whose motive carries the
//! equation back to the looping term — the same convoy every inversion in this
//! chain uses.
//!
//! # Why `D` has a `bvar` domain and not a `sort`
//!
//! `D := lam (bvar 0) (app (bvar 0) (bvar 0))` is ill-typed, and deliberately.
//! `whnf_acc` is a statement about REDUCTION and does not care; what a `sort`
//! domain would cost is a `no_whnf_step_sort` the tree does not have, which is
//! its own fifteen-arm refutation and buys nothing here. The content is
//! entirely in the body, and the body is the same either way.
//!
//! # What is carried
//!
//! Four ι/δ absurdity hypotheses, on the two subterms that could otherwise
//! step: the lambda itself and its neutral body `app (bvar 0) (bvar 0)`. They
//! are carried rather than discharged for the reason everything in this chain
//! carries ι and δ — whether those relations fire on a given shape is a
//! question about them, and the caller answers it. Carrying them as `forall (C
//! : Type), ... -> C` is the tree's own absurdity idiom (`no_whnf_step_bvar`),
//! and it says precisely that a neutral term admitting an ι or δ step would be
//! a defect of that relation.
//!
//! # What this buys
//!
//! The type-blind family becomes PROVABLY not a candidate model rather than
//! not-yet-shown-to-be-one, so every other entry in
//! `designs/2026-09-18-is-candmodel-uninhabited.md`'s map is a positive result
//! about a family whose single failure is pinned. It does NOT say anything
//! about `CandModel`'s inhabitation: a family failing one law is not evidence
//! that no family satisfies all fourteen.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `D`, spelled once. Every use is this literal, because introducing a `def`
/// for it would make `D` a CONSTANT and so give it a δ step to refute — a step
/// that exists only because of the abbreviation.
const OMEGA_LAM: &str = "(KExpr.lam (KExpr.bvar Nat.zero) \
                         (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))";

/// The neutral body, likewise spelled once.
const OMEGA_BODY: &str = "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";

impl Specification {
    /// A term that steps to ITSELF is not accessible. General — no Ω, no
    /// candidate, nothing about this particular `d`.
    fn self_app_loop_not_whnf_acc_src() -> String {
        "def self_app_loop_not_whnf_acc (d : KExpr) \
         (hloop : whnf_step (KExpr.app d d) (KExpr.app d d)) (C : Type) \
         (h : whnf_acc (KExpr.app d d)) : C := \
         @whnf_acc.rec \
         (fun (x : KExpr) (_hx : whnf_acc x) => @Eq KExpr x (KExpr.app d d) -> C) \
         (fun (x : KExpr) \
         (_f : forall (y : KExpr), whnf_step x y -> whnf_acc y) \
         (ih : forall (y : KExpr) (_s : whnf_step x y), \
         @Eq KExpr y (KExpr.app d d) -> C) \
         (heq : @Eq KExpr x (KExpr.app d d)) => \
         ih (KExpr.app d d) \
         (@Eq.substType KExpr \
         (fun (z : KExpr) => whnf_step z (KExpr.app d d)) \
         (KExpr.app d d) x (@Eq.symm KExpr x (KExpr.app d d) heq) hloop) \
         (@Eq.refl KExpr (KExpr.app d d))) \
         (KExpr.app d d) h (@Eq.refl KExpr (KExpr.app d d))"
            .to_string()
    }

    /// `app D D` beta-steps to itself. The only question this asks of the
    /// kernel is whether `instantiate` COMPUTES on closed concrete syntax; the
    /// term is otherwise `whnf_step.beta` over `beta_reduces.beta`.
    fn omega_self_step_src() -> String {
        format!(
            "def omega_self_step : \
             whnf_step (KExpr.app {d} {d}) (KExpr.app {d} {d}) := \
             @whnf_step.beta (KExpr.app {d} {d}) (KExpr.app {d} {d}) \
             (beta_reduces.beta (KExpr.bvar Nat.zero) {body} {d})",
            d = OMEGA_LAM,
            body = OMEGA_BODY,
        )
    }

    /// `D` itself IS accessible — which is what makes the refutation bite.
    /// Both its components are `bvar`-headed and admit no β step, so the whole
    /// proof is two inversions dispatching to `no_whnf_step_bvar` and
    /// `lam_ne_bvar`.
    fn whnf_acc_omega_lam_src() -> String {
        format!(
            "def whnf_acc_omega_lam \
             (kio_lam : forall (z : KExpr) (R : Type), iota_reduces {d} z -> R) \
             (kde_lam : forall (z : KExpr) (R : Type), delta_reduces {d} z -> R) \
             (kio_body : forall (z : KExpr) (R : Type), iota_reduces {body} z -> R) \
             (kde_body : forall (z : KExpr) (R : Type), delta_reduces {body} z -> R) : \
             whnf_acc {d} := \
             whnf_acc.intro {d} \
             (fun (e2 : KExpr) (st : whnf_step {d} e2) => \
             @whnf_step.rec {d} e2 (fun (_h : whnf_step {d} e2) => whnf_acc e2) \
             (fun (hb : beta_reduces {d} e2) => \
             beta_reduces_lam_inv (KExpr.bvar Nat.zero) {body} e2 (whnf_acc e2) hb \
             (fun (A2 : KExpr) (hsA : beta_reduces (KExpr.bvar Nat.zero) A2) \
             (_he : @Eq KExpr e2 (KExpr.lam A2 {body})) => \
             no_whnf_step_bvar Nat.zero A2 (whnf_acc e2) \
             (@whnf_step.beta (KExpr.bvar Nat.zero) A2 hsA)) \
             (fun (b2 : KExpr) (hsb : beta_reduces {body} b2) \
             (_he : @Eq KExpr e2 (KExpr.lam (KExpr.bvar Nat.zero) b2)) => \
             whnf_step_app_inv (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) b2 \
             (whnf_acc e2) (@whnf_step.beta {body} b2 hsb) \
             (fun (A0 : KExpr) (body0 : KExpr) \
             (hl : @Eq KExpr (KExpr.bvar Nat.zero) (KExpr.lam A0 body0)) \
             (_hb : @Eq KExpr b2 (instantiate body0 (KExpr.bvar Nat.zero))) => \
             lam_ne_bvar A0 body0 Nat.zero (whnf_acc e2) \
             (@Eq.symm KExpr (KExpr.bvar Nat.zero) (KExpr.lam A0 body0) hl)) \
             (fun (f2 : KExpr) (hsf : beta_reduces (KExpr.bvar Nat.zero) f2) \
             (_hb : @Eq KExpr b2 (KExpr.app f2 (KExpr.bvar Nat.zero))) => \
             no_whnf_step_bvar Nat.zero f2 (whnf_acc e2) \
             (@whnf_step.beta (KExpr.bvar Nat.zero) f2 hsf)) \
             (fun (a2 : KExpr) (hsa : beta_reduces (KExpr.bvar Nat.zero) a2) \
             (_hb : @Eq KExpr b2 (KExpr.app (KExpr.bvar Nat.zero) a2)) => \
             no_whnf_step_bvar Nat.zero a2 (whnf_acc e2) \
             (@whnf_step.beta (KExpr.bvar Nat.zero) a2 hsa)) \
             (fun (hir : iota_reduces {body} b2) => \
             kio_body b2 (whnf_acc e2) hir) \
             (fun (hdr : delta_reduces {body} b2) => \
             kde_body b2 (whnf_acc e2) hdr)) \
             (fun (hir : iota_reduces {d} e2) => kio_lam e2 (whnf_acc e2) hir)) \
             (fun (hd : delta_reduces {d} e2) => kde_lam e2 (whnf_acc e2) hd) \
             st)",
            d = OMEGA_LAM,
            body = OMEGA_BODY,
        )
    }

    /// **The refutation.** `pi_elim` at the type-blind candidate reads
    /// `whnf_acc f -> whnf_acc a -> whnf_acc (app f a)`; apply it at `f = a =
    /// D` and the conclusion is `whnf_acc (app D D)`, which
    /// `self_app_loop_not_whnf_acc` turns into anything at all.
    fn pi_elim_blind_refuted_src() -> String {
        format!(
            "def pi_elim_blind_refuted \
             (kio_lam : forall (z : KExpr) (R : Type), iota_reduces {d} z -> R) \
             (kde_lam : forall (z : KExpr) (R : Type), delta_reduces {d} z -> R) \
             (kio_body : forall (z : KExpr) (R : Type), iota_reduces {body} z -> R) \
             (kde_body : forall (z : KExpr) (R : Type), delta_reduces {body} z -> R) \
             (C : Type) \
             (hpi : forall (f : KExpr) (a : KExpr), \
             whnf_acc f -> whnf_acc a -> whnf_acc (KExpr.app f a)) : C := \
             self_app_loop_not_whnf_acc {d} omega_self_step C \
             (hpi {d} {d} \
             (whnf_acc_omega_lam kio_lam kde_lam kio_body kde_body) \
             (whnf_acc_omega_lam kio_lam kde_lam kio_body kde_body))",
            d = OMEGA_LAM,
            body = OMEGA_BODY,
        )
    }

    /// A lambda admits no δ step. `delta_step env e e'` is a DEFINITION —
    /// `Eq (OptionType KExpr) (delta_reduct env e) (some e')` — so if
    /// `delta_reduct` computes to `none` on a `lam` (δ fires on a const-headed
    /// spine, and a `lam` is not one), the hypothesis is already an equation
    /// between `none` and `some` and no-confusion closes it.
    ///
    /// This is the same shape `no_whnf_step_const` uses for its δ arm, minus
    /// the `defval` detour that a const needs and a `lam` does not.
    fn no_delta_reduces_lam_src() -> String {
        "def no_delta_reduces_lam (ty : KExpr) (bb : KExpr) (z : KExpr) (C : Type) \
         (h : delta_reduces (KExpr.lam ty bb) z) : C := \
         option_none_ne_some_type KExpr z C \
         (delta_reduces_to_step (KExpr.lam ty bb) z h)"
            .to_string()
    }

    /// A lambda admits no ι step, by the same computation on `iota_reduct`.
    fn no_iota_reduces_lam_src() -> String {
        "def no_iota_reduces_lam (ty : KExpr) (bb : KExpr) (z : KExpr) (C : Type) \
         (h : iota_reduces (KExpr.lam ty bb) z) : C := \
         option_none_ne_some_type KExpr z C \
         (iota_reduces_to_step (KExpr.lam ty bb) z h)"
            .to_string()
    }

    /// A `bvar`-headed application admits no δ step: the spine head is a `bvar`,
    /// so `delta_reduct` finds no constant name to unfold.
    fn no_delta_reduces_bvar_app_src() -> String {
        "def no_delta_reduces_bvar_app (i : Nat) (aa : KExpr) (z : KExpr) (C : Type) \
         (h : delta_reduces (KExpr.app (KExpr.bvar i) aa) z) : C := \
         option_none_ne_some_type KExpr z C \
         (delta_reduces_to_step (KExpr.app (KExpr.bvar i) aa) z h)"
            .to_string()
    }

    /// The same for ι: a `bvar`-headed application is not a recursor
    /// application, so `iota_reduct` finds no rule.
    fn no_iota_reduces_bvar_app_src() -> String {
        "def no_iota_reduces_bvar_app (i : Nat) (aa : KExpr) (z : KExpr) (C : Type) \
         (h : iota_reduces (KExpr.app (KExpr.bvar i) aa) z) : C := \
         option_none_ne_some_type KExpr z C \
         (iota_reduces_to_step (KExpr.app (KExpr.bvar i) aa) z h)"
            .to_string()
    }

    /// `whnf_acc D` with NOTHING carried, if the four discharges above hold.
    fn whnf_acc_omega_lam_uncond_src() -> String {
        format!(
            "def whnf_acc_omega_lam_uncond : whnf_acc {d} := \
             whnf_acc_omega_lam \
             (fun (z : KExpr) (R : Type) (hir : iota_reduces {d} z) => \
             no_iota_reduces_lam (KExpr.bvar Nat.zero) {body} z R hir) \
             (fun (z : KExpr) (R : Type) (hdr : delta_reduces {d} z) => \
             no_delta_reduces_lam (KExpr.bvar Nat.zero) {body} z R hdr) \
             (fun (z : KExpr) (R : Type) (hir : iota_reduces {body} z) => \
             no_iota_reduces_bvar_app Nat.zero (KExpr.bvar Nat.zero) z R hir) \
             (fun (z : KExpr) (R : Type) (hdr : delta_reduces {body} z) => \
             no_delta_reduces_bvar_app Nat.zero (KExpr.bvar Nat.zero) z R hdr)",
            d = OMEGA_LAM,
            body = OMEGA_BODY,
        )
    }

    /// **The refutation, unconditional.** If this elaborates then `pi_elim` at
    /// the type-blind candidate is FALSE outright — not false-modulo-four-
    /// hypotheses — and the type-blind family is PROVABLY not a candidate model.
    fn pi_elim_blind_refuted_uncond_src() -> String {
        format!(
            "def pi_elim_blind_refuted_uncond (C : Type) \
             (hpi : forall (f : KExpr) (a : KExpr), \
             whnf_acc f -> whnf_acc a -> whnf_acc (KExpr.app f a)) : C := \
             self_app_loop_not_whnf_acc {d} omega_self_step C \
             (hpi {d} {d} whnf_acc_omega_lam_uncond whnf_acc_omega_lam_uncond)",
            d = OMEGA_LAM,
        )
    }

    /// All ten measured green in scratch 2026-09-18, then wired — that order is
    /// the recipe, not caution. A wired constant that fails aborts the SPEC
    /// BUILD, which makes every other probe in the same run report nothing;
    /// unwired, the harness names the one that failed. Scratch proves the
    /// terms, wiring proves the order, and doing both in one step proves
    /// neither when it fails.
    pub(super) fn omega_not_sn_sources() -> Vec<(String, String)> {
        vec![
            (
                "self_app_loop_not_whnf_acc".to_string(),
                Self::self_app_loop_not_whnf_acc_src(),
            ),
            ("omega_self_step".to_string(), Self::omega_self_step_src()),
            (
                "whnf_acc_omega_lam".to_string(),
                Self::whnf_acc_omega_lam_src(),
            ),
            (
                "pi_elim_blind_refuted".to_string(),
                Self::pi_elim_blind_refuted_src(),
            ),
            (
                "no_delta_reduces_lam".to_string(),
                Self::no_delta_reduces_lam_src(),
            ),
            (
                "no_iota_reduces_lam".to_string(),
                Self::no_iota_reduces_lam_src(),
            ),
            (
                "no_delta_reduces_bvar_app".to_string(),
                Self::no_delta_reduces_bvar_app_src(),
            ),
            (
                "no_iota_reduces_bvar_app".to_string(),
                Self::no_iota_reduces_bvar_app_src(),
            ),
            (
                "whnf_acc_omega_lam_uncond".to_string(),
                Self::whnf_acc_omega_lam_uncond_src(),
            ),
            (
                "pi_elim_blind_refuted_uncond".to_string(),
                Self::pi_elim_blind_refuted_uncond_src(),
            ),
        ]
    }
    /// Registered after `add_step_app_inversion`, which mints both inversions
    /// `whnf_acc_omega_lam` consumes. Every statement here is about `whnf_acc`
    /// and `whnf_step` alone — there is no candidate in any of them — so these
    /// are wired, and the `CandModel` reading lives in the design note.
    pub(super) fn add_omega_not_sn(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::omega_not_sn_sources() {
            self.add_recursive_def(&src, "omega is not strongly normalizing")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "omega_not_sn_tests.rs"]
mod tests;
