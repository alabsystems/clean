// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **What a `whnf_step` out of an application can be** — the `app` sibling of
//! `whnf_step_let_inv`.
//!
//! ```text
//! whnf_step (app f a) e2
//!   -> e2 is  instantiate body a   with f = lam A0 body        (beta)
//!   or e2 is  app f2 a             with beta_reduces f f2      (congruence, fn)
//!   or e2 is  app f a2             with beta_reduces a a2      (congruence, arg)
//!   or the step is iota or delta   (CARRIED to the caller)
//! ```
//!
//! Five continuations, fifteen `beta_reduces` arms, eleven of them refuted by
//! the `app_ne_*` discrimination family. The shape is copied deliberately from
//! `whnf_step_let_inv`: same convoy carrying BOTH index equations, same reason
//! (`beta_reduces.rec` is applied at fixed indices, so inside an arm the
//! binders are that arm's own indices and the equations are what tie them
//! back), and the same `C : Type` rather than `Prop`, which this non-cumulative
//! kernel forces.
//!
//! # Why it is needed
//!
//! `redAbstraction` — `CandModel`'s β weak-head-expansion law — is the twin of
//! `redLet`, and at a type-blind candidate it reads
//!
//! ```text
//! whnf_acc A -> (forall x, whnf_acc x -> whnf_acc (instantiate b x))
//!   -> forall a, whnf_acc a -> whnf_acc (app (lam A b) a)
//! ```
//!
//! whose proof is the same triple accessibility induction `redlet_blind` runs,
//! with `let_` replaced by `app (lam ...)`. The `let_` version needed
//! `whnf_step_let_inv`; this is what the β version needs. It is a general fact
//! about the step relation and is tied to no candidate, so it is wired.
//!
//! ι and δ are CARRIED, as everywhere in this chain: whether an application can
//! ι- or δ-step is a question about those relations and the caller answers it.
//!
//! # Two inversions, because one is not enough
//!
//! `whnf_step_app_inv`'s fn-congruence continuation hands back `beta_reduces f
//! f2` and says nothing about `f2`. For a β redex `f` is a `lam`, and the
//! accessibility induction needs to know `f2` is still a `lam` and WHICH of its
//! two components moved — that is what routes the step to the induction
//! hypothesis on `A` or the one on `b`. So this module carries a second
//! inversion, `beta_reduces_lam_inv`, and the pair is what the β law needs.
//!
//! The `let_` case needed only one inversion because a `let_` is a single
//! constructor carrying all three components: `whnf_step_let_inv` names the
//! moving one directly. The β redex spreads the same information over two
//! constructors, and that is the whole of the extra cost.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The inversion. Eleven refuted arms, three real ones, one carried.
    pub(super) fn whnf_step_app_inv_src() -> String {
        let ap = "(KExpr.app f aa)";
        let motive = format!(
            "(fun (x : KExpr) (y : KExpr) (_h : beta_reduces x y) => \
             @Eq KExpr x {ap} -> @Eq KExpr y e2 -> C)"
        );
        // Every refuted arm has the same body modulo which discriminator and
        // which reassembled left index; spelling it once keeps the eleven
        // honest, since a copy that refutes the WRONG constructor still
        // typechecks whenever both are absurd.
        let refute = |binders: &str, lhs: &str, call: &str, hy: &str| {
            format!(
                "(fun {binders} (hx : @Eq KExpr {lhs} {ap}) ({hy}) => \
                 {call} C (@Eq.symm KExpr {lhs} {ap} hx))"
            )
        };
        format!(
            "def whnf_step_app_inv (f : KExpr) (aa : KExpr) (e2 : KExpr) (C : Type) \
             (h : whnf_step {ap} e2) \
             (kbeta : forall (A0 : KExpr) (body : KExpr), \
             @Eq KExpr f (KExpr.lam A0 body) -> \
             @Eq KExpr e2 (instantiate body aa) -> C) \
             (kfn : forall (f2 : KExpr), beta_reduces f f2 -> \
             @Eq KExpr e2 (KExpr.app f2 aa) -> C) \
             (karg : forall (a2 : KExpr), beta_reduces aa a2 -> \
             @Eq KExpr e2 (KExpr.app f a2) -> C) \
             (kiota : iota_reduces {ap} e2 -> C) \
             (kdelta : delta_reduces {ap} e2 -> C) : C := \
             @whnf_step.rec {ap} e2 (fun (_hs : whnf_step {ap} e2) => C) \
             (fun (hb : beta_reduces {ap} e2) => \
             @beta_reduces.rec {motive} \
             {a_beta} {a_app_left} {a_app_right} {a_lam_ty} {a_lam_body} \
             {a_pi_dom} {a_pi_cod} {a_fa_dom} {a_fa_cod} {a_zeta} \
             {a_let_ty} {a_let_val} {a_let_body} {a_iota} {a_proj} \
             {ap} e2 hb (@Eq.refl KExpr {ap}) (@Eq.refl KExpr e2)) \
             (fun (hd : delta_reduces {ap} e2) => kdelta hd) \
             h",
            // --- the three real arms ---
            a_beta = format_args!(
                "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) \
                 (hx : @Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {ap}) \
                 (hy : @Eq KExpr (instantiate body arg) e2) => \
                 kbeta A0 body \
                 (@Eq.symm KExpr (KExpr.lam A0 body) f \
                 (app_inj_fst (KExpr.lam A0 body) arg f aa hx)) \
                 (@Eq.substType KExpr \
                 (fun (w : KExpr) => @Eq KExpr e2 (instantiate body w)) arg aa \
                 (app_inj_snd (KExpr.lam A0 body) arg f aa hx) \
                 (@Eq.symm KExpr (instantiate body arg) e2 hy)))"
            ),
            a_app_left = format_args!(
                "(fun (g : KExpr) (g2 : KExpr) (a0 : KExpr) (hs : beta_reduces g g2) \
                 (_ih : @Eq KExpr g {ap} -> @Eq KExpr g2 e2 -> C) \
                 (hx : @Eq KExpr (KExpr.app g a0) {ap}) \
                 (hy : @Eq KExpr (KExpr.app g2 a0) e2) => \
                 kfn g2 \
                 (@Eq.substType KExpr (fun (z : KExpr) => beta_reduces z g2) g f \
                 (app_inj_fst g a0 f aa hx) hs) \
                 (@Eq.substType KExpr \
                 (fun (w : KExpr) => @Eq KExpr e2 (KExpr.app g2 w)) a0 aa \
                 (app_inj_snd g a0 f aa hx) \
                 (@Eq.symm KExpr (KExpr.app g2 a0) e2 hy)))"
            ),
            a_app_right = format_args!(
                "(fun (g : KExpr) (a0 : KExpr) (a2 : KExpr) (hs : beta_reduces a0 a2) \
                 (_ih : @Eq KExpr a0 {ap} -> @Eq KExpr a2 e2 -> C) \
                 (hx : @Eq KExpr (KExpr.app g a0) {ap}) \
                 (hy : @Eq KExpr (KExpr.app g a2) e2) => \
                 karg a2 \
                 (@Eq.substType KExpr (fun (z : KExpr) => beta_reduces z a2) a0 aa \
                 (app_inj_snd g a0 f aa hx) hs) \
                 (@Eq.substType KExpr \
                 (fun (w : KExpr) => @Eq KExpr e2 (KExpr.app w a2)) g f \
                 (app_inj_fst g a0 f aa hx) \
                 (@Eq.symm KExpr (KExpr.app g a2) e2 hy)))"
            ),
            // --- eleven refuted arms: the left index is not an application ---
            a_lam_ty = refute(
                "(ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) \
                 (_ih : @Eq KExpr ty (KExpr.app f aa) -> @Eq KExpr ty2 e2 -> C)",
                "(KExpr.lam ty body)",
                "app_ne_lam f aa ty body",
                "_hy : @Eq KExpr (KExpr.lam ty2 body) e2",
            ),
            a_lam_body = refute(
                "(ty : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.app f aa) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.lam ty body)",
                "app_ne_lam f aa ty body",
                "_hy : @Eq KExpr (KExpr.lam ty body2) e2",
            ),
            a_pi_dom = refute(
                "(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : @Eq KExpr dom (KExpr.app f aa) -> @Eq KExpr dom2 e2 -> C)",
                "(KExpr.pi dom body)",
                "app_ne_pi f aa dom body",
                "_hy : @Eq KExpr (KExpr.pi dom2 body) e2",
            ),
            a_pi_cod = refute(
                "(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.app f aa) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.pi dom body)",
                "app_ne_pi f aa dom body",
                "_hy : @Eq KExpr (KExpr.pi dom body2) e2",
            ),
            a_fa_dom = refute(
                "(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : @Eq KExpr dom (KExpr.app f aa) -> @Eq KExpr dom2 e2 -> C)",
                "(KExpr.forall_ dom body)",
                "app_ne_pi f aa dom body",
                "_hy : @Eq KExpr (KExpr.forall_ dom2 body) e2",
            ),
            a_fa_cod = refute(
                "(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.app f aa) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.forall_ dom body)",
                "app_ne_pi f aa dom body",
                "_hy : @Eq KExpr (KExpr.forall_ dom body2) e2",
            ),
            a_zeta = refute(
                "(ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.let_ ty val body)",
                "app_ne_let f aa ty val body",
                "_hy : @Eq KExpr (instantiate body val) e2",
            ),
            a_let_ty = refute(
                "(ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
                 (_hs : beta_reduces ty ty2) \
                 (_ih : @Eq KExpr ty (KExpr.app f aa) -> @Eq KExpr ty2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "app_ne_let f aa ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty2 val body) e2",
            ),
            a_let_val = refute(
                "(ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
                 (_hs : beta_reduces val val2) \
                 (_ih : @Eq KExpr val (KExpr.app f aa) -> @Eq KExpr val2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "app_ne_let f aa ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty val2 body) e2",
            ),
            a_let_body = refute(
                "(ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
                 (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.app f aa) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "app_ne_let f aa ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty val body2) e2",
            ),
            a_proj = refute(
                "(ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) \
                 (_hs : beta_reduces sub sub2) \
                 (_ih : @Eq KExpr sub (KExpr.app f aa) -> @Eq KExpr sub2 e2 -> C)",
                "(KExpr.proj ps pidx sub)",
                "app_ne_proj f aa ps pidx sub",
                "_hy : @Eq KExpr (KExpr.proj ps pidx sub2) e2",
            ),
            // --- the carried arm: variable left index ---
            a_iota = format_args!(
                "(fun (x : KExpr) (y : KExpr) (hir : iota_reduces x y) \
                 (hx : @Eq KExpr x {ap}) (hy : @Eq KExpr y e2) => \
                 kiota (@Eq.substType KExpr (fun (z : KExpr) => iota_reduces {ap} z) \
                 y e2 hy (@Eq.substType KExpr (fun (z : KExpr) => iota_reduces z y) \
                 x {ap} hx hir)))"
            ),
        )
    }

    /// **What a `beta_reduces` out of a lambda can be** — the second half of
    /// what the β weak-head expansion needs.
    ///
    /// ```text
    /// beta_reduces (lam A b) e2
    ///   -> e2 is  lam A2 b   with beta_reduces A A2
    ///   or e2 is  lam A b2   with beta_reduces b b2
    ///   or the step is iota                        (CARRIED)
    /// ```
    ///
    /// `whnf_step_app_inv`'s `kfn` continuation hands back `beta_reduces f f2`
    /// with nothing said about `f2`'s shape. When `f` is the `lam` of a β
    /// redex, the accessibility induction has to know that `f2` is still a
    /// `lam` and which of its two components moved — otherwise the induction
    /// hypotheses on `A` and `b`, which are what make the recursion
    /// well-founded, cannot be applied. That is what this supplies.
    ///
    /// It inverts `beta_reduces` DIRECTLY rather than `whnf_step`, because that
    /// is the relation `kfn` produces; there is no δ arm to dispatch, δ being a
    /// `whnf_step` constructor and not a `beta_reduces` one.
    pub(super) fn beta_reduces_lam_inv_src() -> String {
        let lm = "(KExpr.lam A b)";
        let motive = format!(
            "(fun (x : KExpr) (y : KExpr) (_h : beta_reduces x y) => \
             @Eq KExpr x {lm} -> @Eq KExpr y e2 -> C)"
        );
        let refute = |binders: &str, lhs: &str, call: &str, hy: &str| {
            format!(
                "(fun {binders} (hx : @Eq KExpr {lhs} {lm}) ({hy}) => \
                 {call} C (@Eq.symm KExpr {lhs} {lm} hx))"
            )
        };
        format!(
            "def beta_reduces_lam_inv (A : KExpr) (b : KExpr) (e2 : KExpr) (C : Type) \
             (h : beta_reduces {lm} e2) \
             (kty : forall (A2 : KExpr), beta_reduces A A2 -> \
             @Eq KExpr e2 (KExpr.lam A2 b) -> C) \
             (kbody : forall (b2 : KExpr), beta_reduces b b2 -> \
             @Eq KExpr e2 (KExpr.lam A b2) -> C) \
             (kiota : iota_reduces {lm} e2 -> C) : C := \
             @beta_reduces.rec {motive} \
             {a_beta} {a_app_left} {a_app_right} {a_lam_ty} {a_lam_body} \
             {a_pi_dom} {a_pi_cod} {a_fa_dom} {a_fa_cod} {a_zeta} \
             {a_let_ty} {a_let_val} {a_let_body} {a_iota} {a_proj} \
             {lm} e2 h (@Eq.refl KExpr {lm}) (@Eq.refl KExpr e2)",
            // --- the two real arms: rebuild through lam injectivity ---
            a_lam_ty = format_args!(
                "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (hs : beta_reduces ty ty2) \
                 (_ih : @Eq KExpr ty {lm} -> @Eq KExpr ty2 e2 -> C) \
                 (hx : @Eq KExpr (KExpr.lam ty body) {lm}) \
                 (hy : @Eq KExpr (KExpr.lam ty2 body) e2) => \
                 kty ty2 \
                 (@Eq.substType KExpr (fun (z : KExpr) => beta_reduces z ty2) ty A \
                 (lam_inj_fst ty body A b hx) hs) \
                 (@Eq.substType KExpr \
                 (fun (w : KExpr) => @Eq KExpr e2 (KExpr.lam ty2 w)) body b \
                 (lam_inj_snd ty body A b hx) \
                 (@Eq.symm KExpr (KExpr.lam ty2 body) e2 hy)))"
            ),
            a_lam_body = format_args!(
                "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body {lm} -> @Eq KExpr body2 e2 -> C) \
                 (hx : @Eq KExpr (KExpr.lam ty body) {lm}) \
                 (hy : @Eq KExpr (KExpr.lam ty body2) e2) => \
                 kbody body2 \
                 (@Eq.substType KExpr (fun (z : KExpr) => beta_reduces z body2) body b \
                 (lam_inj_snd ty body A b hx) hs) \
                 (@Eq.substType KExpr \
                 (fun (w : KExpr) => @Eq KExpr e2 (KExpr.lam w body2)) ty A \
                 (lam_inj_fst ty body A b hx) \
                 (@Eq.symm KExpr (KExpr.lam ty body2) e2 hy)))"
            ),
            // --- twelve refuted arms: the left index is not a lambda ---
            a_beta = refute(
                "(A0 : KExpr) (body : KExpr) (arg : KExpr)",
                "(KExpr.app (KExpr.lam A0 body) arg)",
                "lam_ne_app A b (KExpr.lam A0 body) arg",
                "_hy : @Eq KExpr (instantiate body arg) e2",
            ),
            a_app_left = refute(
                "(g : KExpr) (g2 : KExpr) (a0 : KExpr) (_hs : beta_reduces g g2) \
                 (_ih : @Eq KExpr g (KExpr.lam A b) -> @Eq KExpr g2 e2 -> C)",
                "(KExpr.app g a0)",
                "lam_ne_app A b g a0",
                "_hy : @Eq KExpr (KExpr.app g2 a0) e2",
            ),
            a_app_right = refute(
                "(g : KExpr) (a0 : KExpr) (a2 : KExpr) (_hs : beta_reduces a0 a2) \
                 (_ih : @Eq KExpr a0 (KExpr.lam A b) -> @Eq KExpr a2 e2 -> C)",
                "(KExpr.app g a0)",
                "lam_ne_app A b g a0",
                "_hy : @Eq KExpr (KExpr.app g a2) e2",
            ),
            a_pi_dom = refute(
                "(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : @Eq KExpr dom (KExpr.lam A b) -> @Eq KExpr dom2 e2 -> C)",
                "(KExpr.pi dom body)",
                "lam_ne_pi A b dom body",
                "_hy : @Eq KExpr (KExpr.pi dom2 body) e2",
            ),
            a_pi_cod = refute(
                "(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.lam A b) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.pi dom body)",
                "lam_ne_pi A b dom body",
                "_hy : @Eq KExpr (KExpr.pi dom body2) e2",
            ),
            a_fa_dom = refute(
                "(dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : @Eq KExpr dom (KExpr.lam A b) -> @Eq KExpr dom2 e2 -> C)",
                "(KExpr.forall_ dom body)",
                "lam_ne_pi A b dom body",
                "_hy : @Eq KExpr (KExpr.forall_ dom2 body) e2",
            ),
            a_fa_cod = refute(
                "(dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.lam A b) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.forall_ dom body)",
                "lam_ne_pi A b dom body",
                "_hy : @Eq KExpr (KExpr.forall_ dom body2) e2",
            ),
            a_zeta = refute(
                "(ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.let_ ty val body)",
                "lam_ne_let A b ty val body",
                "_hy : @Eq KExpr (instantiate body val) e2",
            ),
            a_let_ty = refute(
                "(ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
                 (_hs : beta_reduces ty ty2) \
                 (_ih : @Eq KExpr ty (KExpr.lam A b) -> @Eq KExpr ty2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "lam_ne_let A b ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty2 val body) e2",
            ),
            a_let_val = refute(
                "(ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
                 (_hs : beta_reduces val val2) \
                 (_ih : @Eq KExpr val (KExpr.lam A b) -> @Eq KExpr val2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "lam_ne_let A b ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty val2 body) e2",
            ),
            a_let_body = refute(
                "(ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
                 (_hs : beta_reduces body body2) \
                 (_ih : @Eq KExpr body (KExpr.lam A b) -> @Eq KExpr body2 e2 -> C)",
                "(KExpr.let_ ty val body)",
                "lam_ne_let A b ty val body",
                "_hy : @Eq KExpr (KExpr.let_ ty val body2) e2",
            ),
            a_proj = refute(
                "(ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) \
                 (_hs : beta_reduces sub sub2) \
                 (_ih : @Eq KExpr sub (KExpr.lam A b) -> @Eq KExpr sub2 e2 -> C)",
                "(KExpr.proj ps pidx sub)",
                "lam_ne_proj A b ps pidx sub",
                "_hy : @Eq KExpr (KExpr.proj ps pidx sub2) e2",
            ),
            // --- the carried arm ---
            a_iota = format_args!(
                "(fun (x : KExpr) (y : KExpr) (hir : iota_reduces x y) \
                 (hx : @Eq KExpr x {lm}) (hy : @Eq KExpr y e2) => \
                 kiota (@Eq.substType KExpr (fun (z : KExpr) => iota_reduces {lm} z) \
                 y e2 hy (@Eq.substType KExpr (fun (z : KExpr) => iota_reduces z y) \
                 x {lm} hx hir)))"
            ),
        )
    }

    pub(super) fn step_app_inversion_sources() -> Vec<(String, String)> {
        vec![
            (
                "whnf_step_app_inv".to_string(),
                Self::whnf_step_app_inv_src(),
            ),
            (
                "beta_reduces_lam_inv".to_string(),
                Self::beta_reduces_lam_inv_src(),
            ),
        ]
    }

    /// Registered from `bundles.rs` beside the other step-inversion work. Needs
    /// only `beta_reduces` / `whnf_step` and the `app_ne_*` / `app_inj_*`
    /// discrimination families, all of which are earlier.
    pub(super) fn add_step_app_inversion(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::step_app_inversion_sources() {
            self.add_recursive_def(&src, "application step inversion")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "step_app_inversion_tests.rs"]
mod tests;
