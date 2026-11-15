// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **PROBE — `CandModel.redAbstraction` at the type-blind candidate.**
//!
//! ```text
//! whnf_acc A -> (forall x, whnf_acc x -> whnf_acc (instantiate b x))
//!   -> forall a, whnf_acc a -> whnf_acc (app (lam A b) a)
//! ```
//!
//! This is `redAbstraction` with `Red T e := whnf_acc e`, the candidate that
//! discards the type index — the β twin of `redlet_blind`, and the last of the
//! telescope's non-recursor laws to be measured.
//!
//! NOT WIRED, and not to be: `Red T e := whnf_acc e` is not a candidate model
//! (`pi_elim` is false at it), so registering this as a fact about `CandModel`
//! would be a false claim. Its value is diagnostic — it says whether the law is
//! hard INTRINSICALLY or hard BY ROUTE, which is the question
//! `designs/2026-09-18-is-candmodel-uninhabited.md` §3d says the probe can
//! actually decide.
//!
//! # The same triple induction, and one extra inversion
//!
//! `whnf_step` reduces under binders, so `lam_ty`, `lam_body` and `app_right`
//! are all steps out of the redex and each of `A`, `b` and `a` needs its own
//! well-founded recursion — exactly as for ζ. What β needs and ζ did not is a
//! SECOND inversion: the redex spreads its three components over an `app` and a
//! `lam`, so `whnf_step_app_inv`'s fn-congruence case hands back a step of the
//! `lam` and `beta_reduces_lam_inv` is what says which component moved. Both
//! live in `step_app_inversion.rs` and both are wired, being general facts.
//!
//! ι and δ are CARRIED, as everywhere in this chain, and here there are THREE
//! carriers rather than two: ι and δ out of the application, and ι out of the
//! lambda in the function position. That third one has no ζ counterpart and is
//! a direct consequence of the redex being two constructors deep.

use crate::spec::Specification;

impl Specification {
    /// The probe. Structure copied from `redlet_blind` deliberately: same three
    /// motives, same `whnf_acc.intro` at the node, same `Eq.substType` transport
    /// of each reduct's equation onto the goal.
    #[cfg(test)]
    pub(super) fn redabstraction_blind_src() -> String {
        let hyp =
            |bb: &str| format!("forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate {bb} x)");
        let redex =
            |ty: &str, body: &str, arg: &str| format!("(KExpr.app (KExpr.lam {ty} {body}) {arg})");
        let m_b = format!(
            "(fun (bb : KExpr) (_h : whnf_acc bb) => ({}) -> whnf_acc {})",
            hyp("bb"),
            redex("AA", "bb", "aa")
        );
        let m_a = format!(
            "(fun (aa : KExpr) (_h : whnf_acc aa) => \
             forall (bb : KExpr), whnf_acc bb -> ({}) -> whnf_acc {})",
            hyp("bb"),
            redex("AA", "bb", "aa")
        );
        let m_ty = format!(
            "(fun (AA : KExpr) (_h : whnf_acc AA) => \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({}) -> whnf_acc {})",
            hyp("bb"),
            redex("AA", "bb", "aa")
        );
        format!(
            "def redabstraction_blind \
             (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
             iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
             (kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             iota_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
             (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             delta_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
             (klio : forall (p : KExpr) (q : KExpr) (z : KExpr) (r : KExpr), \
             iota_reduces (KExpr.lam p q) z -> whnf_acc (KExpr.app z r)) \
             (A : KExpr) (hA : whnf_acc A) : \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({hyp_bb}) -> whnf_acc {redex_A} := \
             whnf_acc.rec {m_ty} \
             (fun (AA : KExpr) \
             (fA : forall (A2 : KExpr), whnf_step AA A2 -> whnf_acc A2) \
             (ihA : forall (A2 : KExpr) (_s : whnf_step AA A2), \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({hyp_bb}) -> whnf_acc {redex_A2}) \
             (a0 : KExpr) (ha0 : whnf_acc a0) => \
             whnf_acc.rec {m_a} \
             (fun (aa : KExpr) \
             (fa : forall (a2 : KExpr), whnf_step aa a2 -> whnf_acc a2) \
             (iha : forall (a2 : KExpr) (_s : whnf_step aa a2), \
             forall (bb : KExpr), whnf_acc bb -> ({hyp_bb}) -> \
             whnf_acc {redex_a2}) \
             (b0 : KExpr) (hb0 : whnf_acc b0) => \
             whnf_acc.rec {m_b} \
             (fun (bb : KExpr) \
             (fb : forall (b2 : KExpr), whnf_step bb b2 -> whnf_acc b2) \
             (ihb : forall (b2 : KExpr) (_s : whnf_step bb b2), \
             ({hyp_b2}) -> whnf_acc {redex_b2}) \
             (hyp : {hyp_bb}) => \
             whnf_acc.intro {redex_0} \
             (fun (e2 : KExpr) (st : whnf_step {redex_0} e2) => \
             whnf_step_app_inv (KExpr.lam AA bb) aa e2 (whnf_acc e2) st \
             (fun (A0 : KExpr) (body : KExpr) \
             (hl : Eq KExpr (KExpr.lam AA bb) (KExpr.lam A0 body)) \
             (he : Eq KExpr e2 (instantiate body aa)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (instantiate body aa) e2 (Eq.symm KExpr e2 (instantiate body aa) he) \
             (Eq.substType KExpr (fun (w : KExpr) => whnf_acc (instantiate w aa)) \
             bb body (lam_inj_snd AA bb A0 body hl) \
             (hyp aa (whnf_acc.intro aa fa)))) \
             (fun (f2 : KExpr) (hs : beta_reduces (KExpr.lam AA bb) f2) \
             (he : Eq KExpr e2 (KExpr.app f2 aa)) => \
             beta_reduces_lam_inv AA bb f2 (whnf_acc e2) hs \
             (fun (A2 : KExpr) (hsA : beta_reduces AA A2) \
             (hf : Eq KExpr f2 (KExpr.lam A2 bb)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             {redex_A2} e2 \
             (Eq.symm KExpr e2 {redex_A2} \
             (Eq.substType KExpr (fun (w : KExpr) => Eq KExpr e2 (KExpr.app w aa)) \
             f2 (KExpr.lam A2 bb) hf he)) \
             (ihA A2 (whnf_step.beta AA A2 hsA) aa (whnf_acc.intro aa fa) \
             bb (whnf_acc.intro bb fb) hyp)) \
             (fun (b2 : KExpr) (hsb : beta_reduces bb b2) \
             (hf : Eq KExpr f2 (KExpr.lam AA b2)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             {redex_b2} e2 \
             (Eq.symm KExpr e2 {redex_b2} \
             (Eq.substType KExpr (fun (w : KExpr) => Eq KExpr e2 (KExpr.app w aa)) \
             f2 (KExpr.lam AA b2) hf he)) \
             (ihb b2 (whnf_step.beta bb b2 hsb) \
             (instantiate_hyp_step hiota bb b2 hsb hyp))) \
             (fun (hir : iota_reduces (KExpr.lam AA bb) f2) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (KExpr.app f2 aa) e2 (Eq.symm KExpr e2 (KExpr.app f2 aa) he) \
             (klio AA bb f2 aa hir))) \
             (fun (a2 : KExpr) (hsa : beta_reduces aa a2) \
             (he : Eq KExpr e2 {redex_a2}) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             {redex_a2} e2 (Eq.symm KExpr e2 {redex_a2} he) \
             (iha a2 (whnf_step.beta aa a2 hsa) bb (whnf_acc.intro bb fb) hyp)) \
             (fun (hir : iota_reduces {redex_0} e2) => kio AA bb aa e2 hir) \
             (fun (hdr : delta_reduces {redex_0} e2) => kde AA bb aa e2 hdr))) \
             b0 hb0) \
             a0 ha0) \
             A hA",
            hyp_bb = hyp("bb"),
            hyp_b2 = hyp("b2"),
            redex_A = redex("A", "bb", "aa"),
            redex_0 = redex("AA", "bb", "aa"),
            redex_A2 = redex("A2", "bb", "aa"),
            redex_a2 = redex("AA", "bb", "a2"),
            redex_b2 = redex("AA", "b2", "aa"),
        )
    }

    #[cfg(test)]
    pub(super) fn redabstraction_probe_sources() -> Vec<(String, String)> {
        vec![(
            "redabstraction_blind".to_string(),
            Self::redabstraction_blind_src(),
        )]
    }
}

#[cfg(test)]
#[path = "redabstraction_probe_tests.rs"]
mod tests;
