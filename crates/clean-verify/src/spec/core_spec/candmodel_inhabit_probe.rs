// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Which of `CandModel`'s laws does a TYPE-BLIND candidate satisfy?**
//!
//! `CandModel.mk` has never been APPLIED — but do not check that with the bare
//! grep this sentence used to give, because THIS FILE is why it stopped working.
//! Measured 2026-09-18: `grep -rn 'CandModel\.mk' crates/clean-verify/` answers
//! TWO, and both are prose — the doc comment on `CANDMODEL_MK_BINDERS` and the
//! line you are reading. Zero are applications. Blank comments first
//! (`… | grep -vE ':\s*(///|//!|//|\*)'`), which answers empty. The failure mode
//! is the one the Proof soundness rules already name — a scanner over raw text
//! counts MENTIONS — reached by the route those rules do not mention: writing
//! the claim down created the mentions that refute its own test. So the question
//! [`designs/2026-09-18-is-candmodel-uninhabited.md`] puts has never had an
//! experiment run at it. This is the cheapest one available.
//!
//! Take the simplest candidate there is, `Red T e := whnf_acc e`, which ignores
//! the type index entirely, and ask each of the fourteen laws SEPARATELY.
//! Nobody expects it to inhabit `CandModel` — `pi_elim` at a type-blind `Red`
//! reads `whnf_acc f -> whnf_acc a -> whnf_acc (app f a)`, which Ω refutes. The
//! experiment is not about whether it succeeds.
//!
//! **It is about WHICH laws are TRIVIAL there**, which is a weaker and more
//! honest question than which are true, and the distinction matters:
//!
//! * a law that ELABORATES here is trivially satisfied by plain accessibility,
//!   with no type structure doing any work;
//! * a law that REFUSES here has been shown only that THIS term does not prove
//!   it. It says nothing about the law's truth. `pi_elim` is refuted at this
//!   candidate by Ω as a matter of mathematics, but the refusal the probe
//!   prints is a TYPE MISMATCH on a deliberately bogus term, and those are not
//!   the same thing. Do not read a refusal here as a refutation.
//!
//! **That caveat is now CLOSED for `pi_elim`, 2026-09-18.** `omega_not_sn.rs`
//! carries `pi_elim_blind_refuted_uncond`, a kernel-checked, unconditional proof
//! that the law is FALSE at this candidate — not merely unfound. The caveat
//! still binds every OTHER refusal in this file, which is why it stays.
//!
//! MEASURED 2026-09-18, six laws asked: `cr1`, `cr2`, `cr3`, `red_sort` and
//! `redTypeStep` HOLD; `pi_elim` refuses (the control). So **the three Girard
//! candidate conditions the whole ladder is organised around are FREE at a
//! type-blind candidate** — `cr3` is literally `whnf_acc.intro`, `cr2` is its
//! inversion, `cr1` is the identity. They are non-trivial in a real model
//! precisely because the type index is doing work there, and discarding it is
//! what makes them collapse. The content of `CandModel` lives in the other
//! nine.
//!
//! Each law is its own lemma so a failure names the LAW, the same discipline
//! the step-transfer arms used.
//!
//! NOT WIRED, and never to be: `Red T e := whnf_acc e` is not a candidate model
//! and registering these as facts about `CandModel` would be a false claim.
//! They are elaborated by the scratch test beside this file and discarded.
//!
//! There is deliberately NO registrar here. One existed, `#[cfg(test)]` and
//! `#[allow(dead_code)]`, called by nothing — a capability with no caller, and
//! for probes whose own doc says they must never be registered that is not a
//! harmless spare part but the thing most likely to get wired by mistake. The
//! test builds its own spec and adds these to it directly.

use crate::spec::Specification;

impl Specification {
    /// `(name, source)` for each law, at the type-blind candidate.
    #[cfg(test)]
    pub(super) fn candmodel_blind_probe_sources() -> Vec<(String, String)> {
        let acc = |e: &str| format!("whnf_acc {e}");
        vec![
            // cr1 — reducible implies SN. Identity at this candidate.
            (
                "probe_blind_cr1".to_string(),
                format!(
                    "def probe_blind_cr1 (T : KExpr) (e : KExpr) (h : {}) : {} := h",
                    acc("e"),
                    acc("e")
                ),
            ),
            // cr2 — closed under reduction. This is whnf_acc INVERSION: the
            // constructor stores exactly the function being asked for.
            (
                "probe_blind_cr2".to_string(),
                format!(
                    "def probe_blind_cr2 (T : KExpr) (e : KExpr) (e2 : KExpr) (h : {he}) \
                     (s : whnf_step e e2) : {he2} := \
                     @whnf_acc.rec \
                     (fun (x : KExpr) (_hx : whnf_acc x) => \
                     forall (y : KExpr), whnf_step x y -> whnf_acc y) \
                     (fun (x : KExpr) \
                     (f : forall (y : KExpr), whnf_step x y -> whnf_acc y) \
                     (_ih : forall (y : KExpr) (_s : whnf_step x y), \
                     forall (z : KExpr), whnf_step y z -> whnf_acc z) => f) \
                     e h e2 s",
                    he = acc("e"),
                    he2 = acc("e2")
                ),
            ),
            // cr3 — a neutral whose reducts are all in is in. This is whnf_acc
            // INTRO verbatim; the Neutral premise is not even consulted.
            (
                "probe_blind_cr3".to_string(),
                format!(
                    "def probe_blind_cr3 (T : KExpr) (e : KExpr) (_n : Neutral e) \
                     (k : forall (e2 : KExpr), whnf_step e e2 -> {}) : {} := \
                     whnf_acc.intro e k",
                    acc("e2"),
                    acc("e")
                ),
            ),
            // red_sort — the base clause. Identity at this candidate.
            (
                "probe_blind_red_sort".to_string(),
                format!(
                    "def probe_blind_red_sort (n : Level) (e : KExpr) (h : {}) : {} := h",
                    acc("e"),
                    acc("e")
                ),
            ),
            // redTypeStep — candidates respect conversion of the TYPE index.
            // Type-blind, so both directions are the identity.
            (
                "probe_blind_red_type_step".to_string(),
                format!(
                    "def probe_blind_red_type_step (T : KExpr) (T2 : KExpr) (e : KExpr) \
                     (_s : whnf_step T T2) : AndType ({h} -> {h}) ({h} -> {h}) := \
                     @AndType.intro ({h} -> {h}) ({h} -> {h}) \
                     (fun (x : {h}) => x) (fun (x : {h}) => x)",
                    h = acc("e")
                ),
            ),
            // pi_elim — EXPECTED TO FAIL, and it is the control for the whole
            // probe. Type-blind it reads `whnf_acc f -> whnf_acc a ->
            // whnf_acc (app f a)`, which Ω refutes. If this one ELABORATED the
            // experiment would be worthless and something else would be wrong.
            (
                "probe_blind_pi_elim".to_string(),
                format!(
                    "def probe_blind_pi_elim (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) \
                     (_hf : {hf}) (_ha : {ha}) : {hfa} := \
                     whnf_acc.intro (KExpr.app f a) \
                     (fun (e2 : KExpr) (_s : whnf_step (KExpr.app f a) e2) => \
                     whnf_acc.intro e2 (fun (e3 : KExpr) (_s3 : whnf_step e2 e3) => \
                     whnf_acc.intro e3 (fun (e4 : KExpr) (_s4 : whnf_step e3 e4) => \
                     whnf_acc.intro e4 (fun (e5 : KExpr) (_s5 : whnf_step e4 e5) => \
                     whnf_acc.intro e5 (fun (e6 : KExpr) (_s6 : whnf_step e5 e6) => \
                     whnf_acc.intro e6 (fun (e7 : KExpr) (_s7 : whnf_step e6 e7) => \
                     _hf))))))",
                    hf = acc("f"),
                    ha = acc("a"),
                    hfa = acc("(KExpr.app f a)")
                ),
            ),
        ]
    }
}

#[cfg(test)]
#[path = "candmodel_inhabit_probe_tests.rs"]
mod tests;
