// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R19 of the candidate-model construction ladder — **THE FIRST NATIVE
//! SEMANTIC LEMMA**: `val_lift` proved by induction on `WKC`, so it holds at
//! `konst` and `let_` derivations.
//!
//! ## Why this rung
//!
//! R18 carried R14's and R16's semantic stack onto `xval` by TRANSPORT, and
//! priced that honestly: every transported theorem quantifies over `h : WK`, so
//! none of them reaches a `konst`- or `let_`-headed `WKC` derivation, and
//! `r18_lift_at_wkc_probe` pins the refusal. R18 then named the successor:
//! `xval`-native semantics at the two new constructors. This is the first one.
//!
//! **`r19_xval_lift`** is `r18_xval_lift` with one binder changed —
//! `h : WKC D e s` where R18 has `h : WK D e s` — and that binder is the whole
//! rung. The left-hand side reads `wkc_lift` at the derivation itself rather
//! than at an embedding, so nothing scopes the theorem to the image of
//! `r17_wk_wkc` any more.
//!
//! ## A — what the induction cost, arm by arm
//!
//! | arm | closes with | new? |
//! |---|---|---|
//! | `var` | `r19_xval_wkc_lift_var` | yes, and it is three lines |
//! | `sort` | `Eq.refl` | no |
//! | `pi` | `r14_sval_pi_congr` + `r14_venvLift_vcons` | no |
//! | `lam` | `r13_vd_arr_funext` + `r14_venvLift_vcons` | no |
//! | `app` | `r14_vapply_congr` | no |
//! | `konst` | `Eq.refl` | yes |
//! | `let_` | body IH + `r14_venvLift_vcons` + value IH | yes |
//!
//! **Five of the seven arms are R14's `val_lift` arms with `sval` replaced by
//! `xval` and `wk_lift` by `wkc_lift`, reusing R13's and R14's helpers
//! VERBATIM.** That is not luck: `r14_sval_pi_congr`, `r14_vapply_congr`,
//! `r13_vd_arr_funext` and `r14_venvLift_vcons` are all statements about VALUES
//! and VALUATIONS, and not one of them mentions a derivation or a typing
//! judgment. The ladder's semantic helper layer turns out to be indifferent to
//! which shape system it serves, which is the reusable fact this rung
//! establishes.
//!
//! ## B — the `var` arm, and R18 paying for itself
//!
//! R14's `var` arm is its most expensive: `r14_sval_wk_lift_var` is a four-step
//! chain through two `sval`-side cast lemmas, because a lifted variable
//! derivation is a TERM cast wrapped around a SHAPE cast wrapped around
//! `WK.var`. The obvious cost of this rung was re-deriving both cast lemmas on
//! the `xval` side.
//!
//! **They are not needed.** `r17_wkc_lift_var` and the embedding of
//! `r14_wk_lift_var` derive the same judgment, so `r17_xval_irrel` (R17's
//! subsingleton) equates their interpretations, `r18_xval_sval` moves one of
//! them to `sval`, and `r14_sval_wk_lift_var` finishes. Three steps, no new
//! cast machinery. **This is the transfer doing visible work**: R18 is not only
//! a statement about the past, it is the reason the first native rung after it
//! is cheap, and any later native rung inherits the same shortcut wherever a
//! `WK`-side lemma already exists for the object in hand.
//!
//! ## C — the two new arms
//!
//! * **`konst` is `Eq.refl`, and that is the content rather than a gap.**
//!   `lift_at` leaves a constant alone, `wkc_lift`'s `konst` arm rebuilds
//!   `WKC.konst` at the extended shape environment with the same two inertness
//!   proofs, and `xval`'s `konst` clause discards its valuation entirely — an
//!   inert constant denotes the TOP candidate, which R17 proved sound because
//!   `r17_const_no_step` says such a constant admits no `whnf_step` at all. Both
//!   sides are therefore literally `fun e => whnf_acc e`, and weakening has
//!   nothing to say about a denotation that never reads the environment.
//!   `r19_konst_arm_shape_probe` is the control that this `Eq.refl` is reading
//!   the real clause: the same reflexivity claimed at an ARROW shape is refused,
//!   because `WKC.konst` concludes at `Sk.ty` and nowhere else.
//! * **`let_` costs three steps, one more than `lam`.** `xval`'s `let_` clause
//!   reads the valuation extended by the VALUE'S interpretation, not by a bound
//!   variable, so after the body's induction hypothesis and `r14_venvLift_vcons`
//!   there is a third congruence — in the extension value — discharged by the
//!   VALUE's induction hypothesis. The ANNOTATION's hypothesis is unused, which
//!   is worth recording: `xval` does not read a `let_`'s annotation at all, so
//!   the semantic weakening lemma is insensitive to it.
//!
//! ## D — the two measurements that keep this rung honest
//!
//! * **`r19_native_extends_transported`** states R18's `r18_xval_lift` TYPE and
//!   proves it with R19's VALUE. The two are different proofs — one routed
//!   through `sval` and `r14_val_lift`, one an induction on `WKC` — so a rung
//!   that widened the binder while quietly drifting the statement would be
//!   invisible without this, and is not.
//! * **`r19_lift_reaches_konst` / `r19_lift_reaches_let`** instantiate the
//!   native lemma at R17's real `konst` and `let_` witnesses. These are the
//!   constants `r18_xval_lift` has no instance of AT ALL: they are the rung's
//!   whole claim, stated at objects rather than at a quantifier.
//!
//! ## What this rung does NOT do
//!
//! * **Only `val_lift` went native — and CLOSED 2026-09-17 for `psub` and
//!   `inst` by R20.** R20 made the definition this bullet said was needed
//!   (`r20_xvenvSubD`), proved it agrees with `venvSubD` on the embedded
//!   fragment in one line off R18's transfer, and then took `val_psub`,
//!   `val_inst` and the semantic β law native at seven constructors. R19 is
//!   consumed there in exactly ONE place — `r20_xvenvSub_up`'s successor branch
//!   is `r20_xval_lift0` — which is the whole dependency of substitution on
//!   weakening, made visible. STILL transported and still scoped to `h : WK`:
//!   `r18_xval_step`, `r18_xval_step_star`, `r18_xval_conv`. WAS: `r18_xval_psub`,
//!   `r18_xval_inst`, `r18_xval_step`, `r18_xval_step_star` and `r18_xval_conv`
//!   are still transported and still scoped to `h : WK`. `val_psub` is the next
//!   one and it is strictly harder: its statement reads `venvSubD`, which is
//!   `WK`-indexed, so a native `psub` needs a `WKC`-indexed valuation
//!   construction FIRST — the definition R18's own doc declined to invent.
//! * **`proj` and `lit` are still untyped**, there is still no conversion rule,
//!   and `konst` is still restricted to INERT constants.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 5 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking. Axiom closure as R18's —
//! `Quot.sound` and the `Quot` type formers through R13's `spec_funext` at the
//! `lam` arm, every one already inside
//! `spec_axiom_closure::EXPLICIT_FOUNDATIONAL_BASE`.

use std::collections::HashSet;

use super::candmodel_construct_r19_src::{r19_items, R19Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R18's theorem helper, verbatim: one `add_definition` per theorem so the
/// kernel's `add_decl` type-checks the proof term against the declared type.
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

/// `(dependencies, description)` for every R19 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r19_xval_wkc_lift_var" => (
            &[
                "r17_wkc_lift_var",
                "r17_xval_irrel",
                "r18_xval_sval",
                "r14_sval_wk_lift_var",
                "Eq.trans",
            ],
            "THE VAR ARM, BOUGHT WITH R18'S TRANSFER. R14 needed a four-step chain through two \
             sval-side cast lemmas here, because a lifted variable derivation is a term cast \
             around a shape cast around WK.var. This needs none of them: r17_wkc_lift_var and the \
             EMBEDDING of r14_wk_lift_var derive one judgment, R17's subsingleton equates their \
             interpretations, r18_xval_sval moves one to sval, and r14_sval_wk_lift_var finishes. \
             Three steps, no xval-side transport machinery at all.",
        ),
        "r19_xval_lift" => (
            &[
                "WKC.rec",
                "xval",
                "wkc_lift",
                "venvLiftD",
                "r19_xval_wkc_lift_var",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
                "r14_venvLift_vcons",
            ],
            "R14's val_lift AT SEVEN CONSTRUCTORS — the first NATIVE semantic lemma on the WKC \
             lineage, and r18_xval_lift with h : WK widened to h : WKC. Five arms are R14's with \
             sval replaced by xval, reusing R13's and R14's helpers VERBATIM, because every one \
             of those helpers is about VALUES and VALUATIONS and none mentions a derivation. The \
             konst arm is Eq.refl (xval's konst clause discards its valuation, so weakening has \
             nothing to say); the let_ arm costs one step more than lam, because the clause reads \
             the valuation extended by the VALUE's interpretation and the extension value needs \
             its own congruence. The ANNOTATION hypothesis is unused: xval does not read a let_'s \
             annotation.",
        ),
        "r19_native_extends_transported" => (
            &["r19_xval_lift", "r17_wk_wkc"],
            "THE DRIFT CHECK. R18's r18_xval_lift TYPE proved with R19's VALUE. The two are \
             different proofs of overlapping statements — one routed through sval and \
             r14_val_lift, one an induction on WKC — so a rung that widened the binder while \
             quietly drifting the statement would be invisible without this.",
        ),
        "r19_lift_reaches_konst" => (
            &["r19_xval_lift", "r17_konst_witness", "wkc_lift"],
            "THE CLAIM AT AN OBJECT: semantic weakening at R17's REAL inert reflected constant. \
             r18_xval_lift has no instance of this at all, konst derivations not being in the \
             image of r17_wk_wkc.",
        ),
        "r19_lift_reaches_let" => (
            &["r19_xval_lift", "r17_let_witness", "wkc_lift"],
            "The same at R17's let_ witness — the second constructor no embedding reaches.",
        ),
        _ => (
            &[],
            "R19 native semantic weakening: val_lift by induction on WKC.",
        ),
    }
}

impl Specification {
    /// Register R19: `val_lift` proved natively by induction on `WKC`.
    pub(super) fn add_candmodel_construct_r19(&mut self) -> Result<(), SpecError> {
        for item in r19_items() {
            match item {
                R19Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r19_tests.rs"]
mod tests;
