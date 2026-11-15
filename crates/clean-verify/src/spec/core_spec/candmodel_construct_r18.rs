// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R18 of the candidate-model construction ladder — **THE SEMANTIC TRANSFER**:
//! the interpretation R17 built agrees with the one R12-R16 proved things
//! about, and the whole semantic stack moves across.
//!
//! ## Why this rung
//!
//! R17 closed by naming its own next item, in its "What did NOT land" section:
//!
//! > *"No `xval`-side re-derivation of R14/R15's SEMANTIC lemmas. […] What
//! > transfers today is the embedding `r17_wk_wkc` and the shape-level
//! > agreement `r17_shapeOf_agrees_on_wk`; the semantic transfer
//! > (`xval (wk_wkc h) r = sval h r`) is the named next item."*
//!
//! That gap is not cosmetic. R17 moved `const` and `let_` onto the lineage that
//! has the metatheory and carried the OPERATIONS with them (`wkc_lift`,
//! `wkc_psub`, `wkc_inst`, `wkc_step`) — but every SEMANTIC theorem in the
//! ladder (`r14_val_lift`, `r14_val_psub`, `r16_val_step`, `r16_val_step_star`,
//! `r16_val_conv`) still spoke about `sval`. So R17's system had seven
//! constructors and R17's semantics had five theorems about a DIFFERENT
//! function. This rung closes that, and it turns out to close it cheaply.
//!
//! ## A — the transfer, and why every arm was already built
//!
//! **`r18_xval_sval`**:
//!
//! ```text
//! forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D),
//!   Eq (VD s) (xval D e s (r17_wk_wkc D e s h) r) (sval D e s h r)
//! ```
//!
//! An induction on the `WK` derivation. `r17_wk_wkc` maps each of the five
//! constructors to the `WKC` constructor of the same name, and `xval`'s clause
//! at that constructor is `sval`'s clause verbatim, so each arm is a
//! congruence in the induction hypotheses and nothing else:
//!
//! | arm | closes with |
//! |---|---|
//! | `var` | `Eq.refl` — both read the valuation |
//! | `sort` | `Eq.refl` — both denote the top candidate |
//! | `pi` | `r14_sval_pi_congr` (R14) |
//! | `lam` | `r13_vd_arr_funext` (R13) |
//! | `app` | `r14_vapply_congr` (R14) |
//!
//! **The measurement worth keeping: this rung wrote no new semantic
//! machinery.** Every arm is `r14_val_lift`'s arm with the lifting stripped
//! out. R13's funext, built for the corpus's `val_lift`, and R14's two
//! congruence helpers, built for the same lemma, are exactly and only what the
//! transfer needs — including at `lam`, where the two sides are semantic
//! FUNCTIONS agreeing pointwise, the obstruction R12 recorded by name and R13
//! removed. The transfer is NOT definitional: `r18_transfer_refl_probe` (a
//! negative control, registered nowhere) is `Eq.refl` at that statement and the
//! kernel refuses it, because both sides are recursors stuck on a VARIABLE
//! derivation.
//!
//! ## B — what `xval` gets natively, at all seven constructors
//!
//! **`r18_xval_env_congr`** is not a transfer. It is R13's `r13_sval_env_congr`
//! re-run on `xval` itself — `r13_venvD_funext` then one `Eq.cong` — and it
//! therefore holds at `konst` and `let_` derivations too, the two constructors
//! no embedding reaches. One line, and it is the only result in this rung whose
//! scope is the WHOLE of R17's system.
//!
//! ## C — the semantic stack, transferred
//!
//! Six theorems, each the R14/R16 statement with `sval` replaced by `xval` on
//! both sides:
//!
//! * **`r18_xval_step`** / **`r18_xval_step_star`** — R16's ∀-form `val_step`
//!   and its reduction-sequence form. Three-step sandwich: transfer forwards,
//!   apply, transfer back.
//! * **`r18_xval_conv`** — R16's unconditional `val_conv`. The only one whose
//!   conclusion is a MEMBERSHIP rather than an equality, so the transfer is
//!   spent through `Eq.substType` in both directions rather than `Eq.trans`.
//! * **`r18_xval_lift`** / **`r18_xval_psub`** / **`r18_xval_inst`** — R14's
//!   semantic weakening, substitution and instantiation, and the three that
//!   also change the SUBJECT: their left-hand sides read `wkc_lift`,
//!   `wkc_psub` and `wkc_inst`, the seven-constructor operations R17 built,
//!   where R14 reads `wk_lift`/`wk_psub`/`wk_inst`. `r18_xval_inst` spends the
//!   transfer a THIRD time, under `vconsD`, because R14's right-hand side
//!   extends the valuation by an `sval` and the `xval` statement must extend it
//!   by an `xval`.
//!
//! **`r18_xval_lift` is where R17's subsingleton finally pays.** `wkc_lift` at
//! an embedded derivation and the embedding of `wk_lift` derive the SAME
//! judgment by genuinely different routes, and a commutation lemma between the
//! two operations would be a real induction. It is not needed:
//! `r17_wkc_deriv_unique` says any two `WKC` derivations of one judgment are
//! equal, so `r17_xval_irrel` closes that step in ONE application. This is the
//! first consumer `r17_wkc_deriv_unique` has had outside its own rung, and it
//! is the concrete reason the subsingleton was worth keeping when R17 measured
//! that a conversion rule would cost it (`r17_conv_verdict`).
//!
//! ## What this rung does NOT do — read before quoting
//!
//! * **Group C is scoped to the image of `r17_wk_wkc`, and that is stated in
//!   its types, not in prose.** Every theorem in it quantifies over `h : WK D e
//!   s`, so none of them says anything about a `konst`- or `let_`-headed `WKC`
//!   derivation. The scope is pinned rather than argued:
//!   `r18_lift_at_wkc_probe` is `r18_xval_lift` generalised to `hw : WKC D e s`
//!   with the SAME proof term, and the kernel refuses it. The refusal is a
//!   TELESCOPE mismatch, and that is the finding rather than a weakness of the
//!   control: the proof cannot be repaired to fit, because both ingredients it
//!   would have to keep — `wk_lift` and `r14_val_lift` — take a `WK` derivation
//!   and there is nothing to hand them. Closing it needs `xval`-side re-proofs
//!   of R14/R16 by induction on `WKC`, which is a rung of its own and is NOT
//!   what this one did.
//! * **`r18_xval_psub`'s right-hand side still reads `venvSubD`**, whose
//!   substitution hypothesis is `forall i, WK D (sg i) (Dp i)` — a
//!   `WK`-indexed valuation construction. A `WKC`-indexed one is a DEFINITION,
//!   not a corollary of this rung, and inventing it here would put an unproved
//!   `xval`-side object inside a theorem that is otherwise pure transport. So
//!   the substitution lemma transfers on its SUBJECT and not on its valuation.
//! * **`proj` and `lit` are still untyped**, the conversion rule is still not
//!   built, `konst` is still restricted to INERT constants, and the constant
//!   shape environment R17 named as "a rung of its own" is still that.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!   R17's list of what separates `WKC` from `TypingCtx` loses exactly one
//!   entry — the semantic transfer — and keeps every other.
//!
//! ## The named next item
//!
//! **PARTIALLY CLOSED 2026-09-17 by R19, and the split is the useful part.**
//! `r19_xval_lift` is `r18_xval_lift` with `h : WK` widened to `h : WKC` —
//! `val_lift` by induction on `WKC`, konst and let_ arms included, reaching
//! R17's real `konst` and `let_` witnesses by name. Two things it measured
//! belong here. It reused R13's and R14's semantic helpers VERBATIM in five of
//! seven arms, because those helpers speak only about VALUES and VALUATIONS and
//! never about a derivation. And its `var` arm — R14's most expensive, a
//! four-step chain through two cast lemmas — cost three lines, because
//! `r17_xval_irrel` plus THIS rung's transfer reduce it to the `WK`-side lemma
//! that already existed. Every later native rung inherits that shortcut
//! wherever a `WK`-side lemma exists for the object in hand.
//!
//! **STILL OPEN, and R19 says so itself:** `psub`, `inst`, `step`, `step_star`
//! and `conv` are still transported and still scoped to `h : WK`. `val_psub` is
//! the next one and it is strictly harder than `val_lift` was — its statement
//! reads `venvSubD`, which is `WK`-indexed, so it needs a `WKC`-indexed
//! valuation construction FIRST, and that is a DEFINITION rather than a
//! corollary. WAS: **`xval`-NATIVE semantics at `konst` and `let_`.** Group B shows the shape
//! of it — `r18_xval_env_congr` is native and costs one line — and Group C's
//! refusal probe shows exactly what is missing: a `val_step`/`val_conv`/
//! `val_lift` proved by induction on `WKC` rather than transported through
//! `r17_wk_wkc`. Two things are known about that rung before it starts. Its
//! `konst` arm should be cheap, because `r17_const_no_step` says an inert
//! constant admits no `whnf_step` at all, so the reduction-side lemmas have
//! nothing to prove there. Its `let_` arm should be cheap for the opposite
//! reason: `r17_xval_zeta` is `Eq.refl`, so the semantic ζ law is definitional.
//! What is NOT known is whether `wkc_step`'s ζ arm and the `xval` `let_` clause
//! line up the way head-β and the `lam`/`app` pair do — R17 designed the binder
//! slot to carry the VALUE's shape precisely so that they would, and that
//! design decision has not yet been cashed on the semantic side.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 10 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking. The transfer's axiom
//! closure is `Quot.sound` plus the `Quot` type formers, inherited through
//! R13's `spec_funext` at the `lam` arm — every one of them already inside
//! `spec_axiom_closure::EXPLICIT_FOUNDATIONAL_BASE`, and the same closure
//! `r14_val_lift` has carried since R14.

use std::collections::HashSet;

use super::candmodel_construct_r18_src::{r18_items, R18Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R17's theorem helper, verbatim: one `add_definition` per theorem so the
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

/// `(dependencies, description)` for every R18 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r18_xval_sval" => (
            &[
                "WK.rec",
                "xval",
                "sval",
                "r17_wk_wkc",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
                "Eq.refl",
            ],
            "THE SEMANTIC TRANSFER. On every term the OLD system types, R17's seven-constructor \
             interpretation and R12's five-constructor one agree, at every valuation — the \
             semantic counterpart of r17_shapeOf_agrees_on_wk. Induction on the WK derivation; \
             var and sort are Eq.refl, pi and app are R14's two congruence helpers, and lam is \
             R13's funext at the arrow shape. NO new semantic machinery: every arm is \
             r14_val_lift's arm with the lifting stripped out. NOT definitional — Eq.refl at this \
             statement is refused, because both sides are recursors stuck on a variable \
             derivation.",
        ),
        "r18_xval_env_congr" => (
            &["xval", "r13_venvD_funext", "Eq.cong"],
            "NATIVE, AT ALL SEVEN CONSTRUCTORS. xval respects pointwise-equal valuations — R13's \
             r13_sval_env_congr re-run on xval itself, so it holds at konst and let_ derivations \
             too, which no embedding reaches. The only result in R18 whose scope is the whole of \
             R17's system.",
        ),
        "r18_xval_step" => (
            &["r18_xval_sval", "r16_val_step", "Eq.trans", "Eq.symm"],
            "R16's forall-form val_step on the xval side. Transfer forwards, apply, transfer \
             back. Scoped to the image of r17_wk_wkc, and its type says so.",
        ),
        "r18_xval_step_star" => (
            &["r18_xval_sval", "r16_val_step_star", "Eq.trans", "Eq.symm"],
            "The same along a whole whnfStar sequence, off R16's val_step_star.",
        ),
        "r18_xval_conv" => (
            &["r18_xval_sval", "r16_val_conv", "Eq.substType", "Eq.symm"],
            "R16's UNCONDITIONAL val_conv on the xval side. The only transfer whose conclusion is \
             a MEMBERSHIP rather than an equality, so the transfer is spent through Eq.substType \
             in both directions rather than Eq.trans.",
        ),
        "r18_xval_lift" => (
            &[
                "r18_xval_sval",
                "r14_val_lift",
                "r17_xval_irrel",
                "wkc_lift",
                "wk_lift",
                "venvLiftD",
                "Eq.trans",
                "Eq.symm",
            ],
            "THE SEMANTIC WEAKENING LEMMA, ON R17'S OWN OPERATION. The one transfer that also \
             changes the SUBJECT: its left-hand side reads wkc_lift, the seven-constructor \
             operation R17 built, where r14_val_lift reads wk_lift. The two derive the SAME \
             judgment by different routes and a commutation lemma would be a real induction — \
             r17_wkc_deriv_unique makes it one application of r17_xval_irrel. FIRST consumer of \
             the subsingleton outside R17, and the concrete reason it was worth keeping when a \
             conversion rule would have cost it.",
        ),
        "r18_xval_psub" => (
            &[
                "r18_xval_sval",
                "r14_val_psub",
                "r17_xval_irrel",
                "wkc_psub",
                "wk_psub",
                "venvSubD",
                "Eq.trans",
                "Eq.symm",
            ],
            "R14's semantic SUBSTITUTION lemma, on wkc_psub. Same four-step chain as \
             r18_xval_lift and for the same reason — the subsingleton identifies wkc_psub at an \
             embedded derivation with the embedding of wk_psub. The right-hand side still reads \
             venvSubD, which is WK-indexed: a WKC-indexed valuation construction is a DEFINITION, \
             not a corollary of this rung.",
        ),
        "r18_xval_inst" => (
            &[
                "r18_xval_sval",
                "r14_val_inst",
                "r17_xval_irrel",
                "wkc_inst",
                "wk_inst",
                "vconsD",
                "Eq.cong",
                "Eq.trans",
                "Eq.symm",
            ],
            "R14's INSTANTIATION lemma, on wkc_inst. FIVE steps, not four: R14 extends the \
             valuation by an sval and the xval statement must extend it by an xval, so the \
             transfer is spent a third time UNDER vconsD through one Eq.cong in the extension \
             value. The only place in R18 where the transfer is used other than at a theorem's \
             own subject.",
        ),
        "r18_transfer_witness" => (
            &["r18_xval_sval", "r12_betaDeriv", "r12_betaJunkEnv"],
            "NON-VACUITY: the transfer at R12's registered beta redex and its derivation — a real \
             application of a real lambda under the all-junk valuation.",
        ),
        "r18_xval_step_witness" => (
            &["r18_xval_step", "r14_beta_step", "r15_instDeriv", "r12_betaDeriv"],
            "r18_xval_step COMPUTED at R12's redex and its contractum — R16's r16_val_step_witness \
             with BOTH interpretations moved to xval.",
        ),
        _ => (
            &[],
            "R18 semantic transfer: xval agrees with sval on the embedded fragment.",
        ),
    }
}

impl Specification {
    /// Register R18: the semantic transfer, and the R14/R16 semantic stack
    /// carried across it onto `xval`.
    pub(super) fn add_candmodel_construct_r18(&mut self) -> Result<(), SpecError> {
        for item in r18_items() {
            match item {
                R18Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r18_tests.rs"]
mod tests;
