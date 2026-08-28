// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R15 of the candidate-model construction ladder — **subject reduction for
//! shapes (`wk_step`), and the `val_step` arms it unlocks.**
//!
//! ## Why this rung
//!
//! R14 closed with a precise handoff:
//!
//! > *"NOT landed: the `piA`/`piB`/`lamA`/`lamB`/`appL`/`appR` arms of
//! > `val_step`, and `val_conv`. They need `wk_step` (subject reduction for
//! > shapes), which needs inversion of the spec's `whnf_step` — δ/ι/ζ/`let_`/
//! > `proj`/`forall_` over a **nine**-constructor `KExpr`, not the corpus's
//! > five-constructor `Step`. Own rung; not claimed."*
//!
//! That is exactly this rung, and the asymmetry R14 pointed at is what makes it
//! cheap: `WK` has five constructors, so most of `whnf_step`'s nine-constructor
//! reach is **absurd** at a `WK`-typed subject.
//!
//! ## A — `wk_step`, and the idiom that paid for it
//!
//! `wk_step : WK D e s -> whnf_step e e2 -> WK D e2 s`. Unconditional, total,
//! at every shape environment, term and shape; registered as a `def` so a later
//! rung can reduce through it.
//!
//! R1/R3/R5's inversion scaffold (`beta_inv_body`) discharges each of
//! `beta_reduces`'s fifteen arms with a hand-written `X_ne_Y` discrimination
//! lemma and recovers the live arm's components through `X_inj_*`. R15 does
//! **neither**. Every inversion here is a **computed motive** — R12's `Neutral`
//! (`dependent_sn_richmodel.rs:378`) read as an inversion principle:
//!
//! * **`r15_stepT C e g2`** is a `KExpr.rec` on the SUBJECT that maps `app` /
//!   `lam` / `pi` to the continuation-passing case analysis those heads deserve,
//!   `bvar` / `sort` to `C` outright (no rule fires, so the inversion IS
//!   `no_whnf_step_bvar` and its missing `sort` counterpart), and `const` /
//!   `let_` / `proj` / `lit` to `ConstFreeUnit`. A dead arm of the fifteen then
//!   discharges by **`ConstFreeUnit.triv`** — the impossible case is killed by
//!   *computation*, exactly as the task's R3/R4 precedent asks — and a live arm
//!   hands its own constructor fields to the continuation with **`Eq.refl`**
//!   instead of recovering them through injectivity. Fourteen of fifteen arms
//!   are one token.
//! * **The ι arm is the only one whose subject is a variable**, so the only one
//!   the computed motive cannot discharge. It is killed by
//!   `iota_step_head_none_absurd_type` on the head-free hypothesis, and
//!   `whnf_step`'s δ leg by `delta_step_head_none_absurd_type` on the same one.
//! * **`r15_headFree_wk`** supplies that hypothesis and is the rung's one real
//!   structural fact: `WK` has no `const` constructor, so the head of a
//!   shape-typed application spine is a `bvar`, a `sort`, a `pi` or a `lam` —
//!   never a constant. Four of its five `WK.rec` arms are `Eq.refl`; the `app`
//!   arm is `headFree_app`, which is definitionally the identity.
//! * **`r15_wkLamT` / `r15_wk_lam_inv`** are the same idiom one level in — a
//!   `KExpr.rec` on the term nested with a `Sk.rec` on the shape — and they are
//!   what the head-β arm needs: from `WK D (lam A b) (Sk.arr d c)` they hand
//!   back `WK (skcons d D) b c` with no `Sk`-injectivity anywhere, because the
//!   `Sk.rec` dispatches on `Sk.arr d c` directly. The contractum's derivation
//!   is then **R14's `wk_inst`**, at the kernel's own `instantiate`.
//!
//! ## B — the payoff
//!
//! * **The six named arms of `val_step`, at given derivations**:
//!   `r15_val_step_piA`, `r15_val_step_piB`, `r15_val_step_lamA`,
//!   `r15_val_step_lamB`, `r15_val_step_appL`, `r15_val_step_appR`. These are
//!   R13's extensionality and R14's operations doing precisely what they were
//!   built for: `r14_sval_pi_congr` for the two Π arms, `r13_vd_arr_funext` for
//!   `lamB`, `r14_vapply_congr` for the two application arms. **`lamA` needs no
//!   hypothesis at all** — the `lam` clause of `sval` never reads the domain
//!   annotation's value, so the arm is `Eq.refl`, and that inertness is now
//!   machine-visible rather than folklore.
//! * **`r15_val_step_sem` — the fused theorem, and the real result.** Subject
//!   reduction AND semantic invariance in ONE `WK.rec`: for every step there is
//!   a reduct derivation whose interpretation agrees with the subject's at
//!   EVERY valuation. `r15_val_star_sem` closes it under whole reduction
//!   sequences (`whnfStar`), `r15_sval_transports_any_step` reads it as
//!   membership transport across an ARBITRARY `whnf_step` — R14 had this only
//!   at head-β — and `r15_conv_contrast` pairs R11's refutation with a
//!   transport across a REAL CONGRUENCE step (`r15_piCongr_step`:
//!   `pi r12_betaRedex (sort 0)` contracting in its domain) in one
//!   kernel-checked constant, the `r12_conv_contrast` pattern at the arm class
//!   R14 could not touch.
//!
//! ## THE OBSTRUCTION THIS RUNG NAMES — read before quoting `val_step`
//!
//! **The ∀-form of `val_step` is not available, and the reason is structural,
//! not effort.** The corpus's `val_step` (FWK.lean:290) reads
//! `val e' r = val e r` with NO derivation in it, because the corpus's `val`
//! recurses on the TERM. R12's `sval` recurses on the DERIVATION, so spec-side
//! the statement must name a derivation for the reduct, and there are exactly
//! two ways to do it:
//!
//! 1. **at `wk_step`'s own output** — `sval e2 (wk_step h st) r = sval e h r`.
//!    Unstatable-as-proved: `wk_step` recurses on `h`, and in any induction the
//!    step `st` is a VARIABLE, so `wk_step`'s arm body is the CPS inversion
//!    applied to a stuck argument and `sval` at it never reduces. No amount of
//!    rearranging the induction changes this; it is why the semantic content
//!    has to be carried by the SAME recursion, which is what `r15_val_step_sem`
//!    does.
//! 2. **at an arbitrary derivation of the reduct** — `forall h2, sval e2 h2 r =
//!    sval e h r`. That is the fused theorem PLUS **`sval` derivation
//!    irrelevance** (`forall (h1 h2 : WK D e s) r, sval D e s h1 r =
//!    sval D e s h2 r`), which this rung does not claim.
//!
//! `val_conv` sits behind the same gap, and the rung makes that precise rather
//! than prose: **`r15_val_conv_from_irrel`** proves, kernel-checked, that
//! derivation irrelevance is the ONLY missing ingredient — two shape-typed
//! terms with a common reduct have the same membership, conditionally on it.
//! Confluence is NOT additionally needed for the joinable form; R14's note that
//! `val_conv` "additionally needs confluence" applies to the closure of
//! `whnfStar` under symmetry, not to this statement.
//!
//! The route to irrelevance is now short and is stated here for the next rung:
//! the same computed-motive idiom gives `sval`-valued inversions at all five
//! `WK` heads (`r15_sval_lam_inv` is the one this rung needed), and irrelevance
//! is a `WK.rec` on `h1` consuming them — with `r15_wk_shape_unique`
//! (`WK D e s1 -> WK D e s2 -> Eq Sk s1 s2`) first, because the `app` arm's
//! inversion produces a domain shape that must be identified with the one in
//! hand before the induction hypothesis applies.
//!
//! ## What is untouched
//!
//! * **R10's `cr3` refutation and R11's `candInterp` conversion refutation
//!   stand.** Nothing here is about `candInterp`. `r15_conv_contrast` RE-ASSERTS
//!   R11 rather than repairing it: the positive result is conversion-invariance
//!   for **`sval`**, a different interpretation, on shape-typed terms only.
//! * **R12's TWO HORNS stand** — HORN 1 (predicativity: `piCandV` lands one
//!   universe above the candidates) and HORN 2 (the derivation-indexed clause
//!   calls `sval` at derivations of unrelated terms, so it is not structural).
//!   Subject reduction is neither, exactly as extensionality (R13) and
//!   substitution (R14) were neither.
//! * **No SN capstone, and `sval` is still PARTIAL.** `WK` types five of
//!   `KExpr`'s nine constructors. Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## What still separates `WK` from `TypingCtx`, updated
//!
//! R14's list minus the one item this rung closes. `WK` still has five
//! constructors against `KExpr`'s NINE (no `const`, `let_`, `proj`, `lit`); it
//! still has **no conversion rule**, so shape assignment is syntax-directed;
//! its context is `Nat -> Sk` — shapes, not types — and `piShape` still erases
//! the codomain's dependence; levels are still semantically inert; `sval` is
//! still partial where a `CandModel` law quantifies over all untyped `KExpr`;
//! and there is still no SN capstone from `WK` alone. **No longer on the list:**
//! SUBJECT REDUCTION. `WK` now has weakening, substitution, instantiation AND
//! subject reduction as operations, and an interpretation that respects all
//! four. **New on the list, and it is the single named gap:** `sval`
//! DERIVATION IRRELEVANCE, which separates the fused `val_step` from its
//! ∀-form and is the whole of what `val_conv` still wants.
//!
//! ## Census
//!
//! ZERO new axioms. 31 constants — 12 `add_recursive_def` and 19 value-bearing
//! theorems through `add_definition` with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r15_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R14's theorem helper, verbatim: one `add_definition` per theorem so the
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

/// `(dependencies, description)` for every R15 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
#[allow(clippy::too_many_lines)]
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r15_headFree_wk" => (
            &["WK.rec", "HeadFree", "headFree_app"],
            "WK NEVER TYPES A CONST-HEADED SPINE: every shape-typed term is HeadFree. WK has five \
             constructors and KExpr.const is not among them, so kapp_fn of a WK-typed term is a \
             bvar, a sort, a pi or a lam. This one fact kills BOTH the delta arm of whnf_step and \
             the iota arm of beta_reduces at a WK-typed subject, which is why subject reduction \
             here needs no reasoning about the_red_env at all. Four of its five WK.rec arms are \
             Eq.refl; the app arm is headFree_app, definitionally the identity.",
        ),
        "r15_stepT" => (
            &["KExpr.rec", "beta_reduces", "instantiate", "ConstFreeUnit"],
            "THE COMPUTED STEP INVERSION. A KExpr.rec on the SUBJECT's head constructor: app / lam \
             / pi get the continuation-passing case analysis of their reducts, bvar / sort get C \
             outright (no rule fires), and const / let_ / proj / lit get ConstFreeUnit. This is \
             R12's Neutral (dependent_sn_richmodel.rs:378) read as an inversion principle, and it \
             replaces the whole X_ne_Y / X_inj_* scaffold R1/R3/R5's beta_inv_body needs: an \
             impossible arm is killed by COMPUTATION and a live arm hands its own constructor \
             fields to the continuation by Eq.refl.",
        ),
        "r15_beta_stepT_inv" => (
            &[
                "beta_reduces.rec",
                "r15_stepT",
                "iota_step_head_none_absurd_type",
                "iota_reduces_to_step",
            ],
            "The complete 15-arm beta_reduces inversion at a head-free subject. Fourteen arms are \
             a single token — ConstFreeUnit.triv for the let_/proj heads, one continuation call \
             with Eq.refl for the live ones. The forall_ congruences land in the SAME arm as \
             pi_dom/pi_cod because KExpr.forall_ is a REDUCIBLE alias for KExpr.pi. The iota arm \
             is the only one whose subject is a variable, hence the only one the computed motive \
             cannot discharge; head-freeness kills it.",
        ),
        "r15_whnf_stepT_inv" => (
            &[
                "whnf_step.rec",
                "r15_beta_stepT_inv",
                "delta_step_head_none_absurd_type",
                "delta_reduces_to_step",
            ],
            "The same at whnf_step: the beta leg is r15_beta_stepT_inv, the DELTA leg is absurd \
             because a delta redex is const-headed and a WK-typed term is not.",
        ),
        "r15_wkLamT" => (
            &["KExpr.rec", "Sk.rec", "WK", "skcons"],
            "The computed WK-inversion at a lambda: KExpr.rec on the term nested with Sk.rec on \
             the shape, so WK D (lam A b) (Sk.arr d c) yields WK (skcons d D) b c with NO \
             Sk-injectivity anywhere — the Sk.rec dispatches on Sk.arr d c directly. Every other \
             head/shape pair is ConstFreeUnit.",
        ),
        "r15_wk_lam_inv" => (
            &["WK.rec", "r15_wkLamT"],
            "That inversion, proved by WK.rec. Four of five arms are ConstFreeUnit.triv; the lam \
             arm hands back its own body derivation. Registered as a def, not a theorem, so \
             wk_step's beta arm can reduce through it.",
        ),
        "wk_step" => (
            &[
                "WK.rec",
                "r15_whnf_stepT_inv",
                "r15_headFree_wk",
                "r15_wk_lam_inv",
                "wk_inst",
                "r14_wkCastT",
            ],
            "SUBJECT REDUCTION FOR SHAPES — the constant this rung exists for, and the single gap \
             R14 named between its rung and val_step/val_conv. WK D e s and one whnf_step e e2 \
             give WK D e2 s: the shape is PRESERVED, not merely related. Every arm calls the one \
             computed inversion; the congruence arms re-type the stepped component at the SAME \
             shape through the induction hypothesis, and the head-beta arm is R14's wk_inst at the \
             kernel's own instantiate. Registered as a def so a later rung can reduce through it.",
        ),
        "r15_val_step_piA" => (
            &["r14_sval_pi_congr"],
            "The piA arm of the corpus's val_step (FWK.lean:295), at given derivations: a step in \
             the DOMAIN of a Pi moves the interpretation only through the domain's value. One of \
             the six arms R14 recorded as not landed.",
        ),
        "r15_val_step_piB" => (
            &["r14_sval_pi_congr"],
            "The piB arm: a step in the CODOMAIN, consumed at the junk-probe valuation extension \
             that sval's Pi clause uses.",
        ),
        "r15_val_step_lamA" => (
            &["sval"],
            "THE ANNOTATION IS SEMANTICALLY INERT. The lam clause of sval never reads the domain \
             annotation's value, so this arm needs NO hypothesis — it is Eq.refl. The corpus's \
             lamA case carries a val_step hypothesis it does not use; here the fact is \
             machine-visible.",
        ),
        "r15_val_step_lamB" => (
            &["r13_vd_arr_funext"],
            "The lamB arm: pointwise agreement of the two bodies at every extended valuation, \
             turned into equality of the two SEMANTIC FUNCTIONS by R13's arrow-shape \
             extensionality. This is the case R12 recorded as blocked by the missing funext.",
        ),
        "r15_val_step_appL" | "r15_val_step_appR" => (
            &["r14_vapply_congr"],
            "The appL / appR arms: semantic application is a congruence in each slot, which is \
             exactly the combinator R14 built for them.",
        ),
        "r15_svalLamT" => (
            &["KExpr.rec", "Sk.rec", "sval", "vconsD"],
            "The SEMANTIC lambda inversion type: the same computed case analysis, but the \
             continuation also receives the lambda's interpretation as the semantic function it \
             denotes. The valuation is quantified INSIDE the continuation, not fixed outside, \
             which is what lets r15_val_step_sem hand its caller one derivation good for every r.",
        ),
        "r15_sval_lam_inv" => (
            &["WK.rec", "r15_svalLamT", "sval"],
            "That inversion, proved by WK.rec. The lam arm's semantic equation is Eq.refl: sval at \
             WK.lam iota-reduces to exactly the semantic function the statement names.",
        ),
        "r15_val_step_sem" => (
            &[
                "WK.rec",
                "r15_whnf_stepT_inv",
                "r15_sval_lam_inv",
                "r14_sval_cast_term",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r14_val_inst",
                "r13_vd_arr_funext",
                "wk_inst",
            ],
            "THE FUSED THEOREM, and the real result of the rung: subject reduction AND semantic \
             invariance in ONE WK.rec. For every whnf_step out of a shape-typed term there is a \
             derivation of the reduct whose interpretation agrees with the subject's at EVERY \
             valuation. It is fused for a structural reason, not for convenience: a CPS inversion \
             is opaque in its result, so sval at wk_step's output does not reduce and a SEPARATE \
             semantic lemma about wk_step is unstatable. All six congruence arms plus head-beta \
             are proved here; head-beta runs on R14's r14_val_inst and r15_sval_lam_inv.",
        ),
        "r15_val_star_sem" => (
            &["whnfStar.rec", "r15_val_step_sem"],
            "The fused theorem closed under whole reduction SEQUENCES, by induction on R1's \
             whnfStar. The refl arm returns the derivation it was given; the step arm composes two \
             interpretations by Eq.trans.",
        ),
        "r15_instDeriv" | "r15_piCodDeriv" | "r15_piRedexDeriv" | "r15_piReductDeriv" => (
            &["wk_inst", "WK.pi", "r12_betaDeriv"],
            "The CONCRETE derivations the contrast is stated at: the contractum of R12's own \
             shape-typed beta redex (through R14's wk_inst), and the two Pi derivations whose \
             DOMAIN is that redex before and after it contracts.",
        ),
        "r15_piCongr_step" => (
            &["whnf_step.beta", "beta_reduces.pi_dom", "beta_reduces.beta"],
            "A real CONGRUENCE step: `pi r12_betaRedex (sort 0)` contracts in its DOMAIN. This is \
             the arm class R14 could not touch — its contrast is at a head-beta redex, which is \
             the one arm it already had.",
        ),
        "r15_svalStepTransports" => (
            &["vcarD", "sval", "r15_piRedexDeriv", "r15_piReductDeriv"],
            "The membership-transport statement across that congruence step, as a named Type so it \
             can sit inside an AndType beside R11's refutation — the r12_svalTransportsBeta idiom. \
             It is CONCRETE for a MEASURED reason (2026-08-27, first cycle): every generic \
             statement of this rung quantifies over a valuation, VEnvD D is Type 1, and a `def … : \
             Type` carrying one is refused with \"expected Type, got Type 1\". That universe fact \
             is why r12_conv_contrast pairs concrete statements and why this one does too.",
        ),
        "r15_sval_transports_congr_step" => (
            &["r15_val_step_piA", "r14_val_beta", "Eq.substType"],
            "That transport, PROVED — r15_val_step_piA at the concrete congruence step, with the \
             domain's semantic equation supplied by R14's r14_val_beta. It is the piA arm doing \
             exactly the job it was landed for, at a real reduction.",
        ),
        "r15_sval_transports_any_step" => (
            &["r15_val_step_sem", "vcarD", "Eq.substType"],
            "THE CONTRAST WITH R11, AT AN ARBITRARY STEP: sval-membership survives ONE whnf_step \
             at ANY shape-typed subject, where R14's r14_sval_transports_real_beta had it only at \
             a head-beta redex. r11_candInterp_step_conv_refuted proves candInterp cannot \
             transport membership across even one whnf_step of the type.",
        ),
        "r15_sval_transports_star" => (
            &["r15_val_star_sem", "vcarD", "Eq.substType"],
            "The same along a whole reduction sequence.",
        ),
        "r15_val_conv_from_irrel" => (
            &["r15_val_star_sem", "vcarD", "Eq.substType", "whnfStar"],
            "val_conv, EXACTLY AS FAR AS IT GOES, and the rung's honest boundary as a \
             kernel-checked constant rather than as prose: two shape-typed terms with a COMMON \
             reduct have the same membership, CONDITIONALLY on sval being independent of which \
             derivation witnesses a term's shape. Derivation irrelevance is the only missing \
             ingredient — confluence is NOT additionally needed for this joinable form.",
        ),
        "r15_conv_contrast" => (
            &[
                "AndType.intro",
                "r11_candInterp_step_conv_refuted",
                "r15_sval_transports_any_step",
            ],
            "R12's r12_conv_contrast pattern one rung on: R11's refutation of \
             conversion-invariance for candInterp and this rung's ARBITRARY-step transport for \
             sval, paired in ONE kernel-checked constant. It RE-ASSERTS R11 rather than repairing \
             it — the positive result is about a different interpretation, on shape-typed terms \
             only.",
        ),
        "r15_wk_step_witness" => (
            &["wk_step", "r12_betaDeriv", "r14_beta_step"],
            "NON-VACUITY: subject reduction applied at R12's own registered shape-typed redex and \
             R14's real head-beta whnf_step.",
        ),
        "r15_wk_step_sort" => (
            &["r15_wk_step_witness", "r12_beta_contractum_is_arg"],
            "THE DISCRIMINATING FORM: the contractum really is sort 0 and it really carries the \
             kind-of-kinds shape. The paired refusal test feeds the kernel the same reduction \
             claimed at Sk.ty and asserts REJECTION, so the witness is not compatible with a \
             wk_step that lost or changed the shape.",
        ),
        "r15_step_transport_witness" => (
            &["r15_sval_transports_any_step", "r12_betaDeriv"],
            "Membership transport COMPUTED at R12's registered redex through the fused theorem, \
             rather than assumed.",
        ),
        _ => (&[], "R15 subject reduction for shapes."),
    }
}

impl Specification {
    /// Register R15: subject reduction for shapes and the `val_step` arms.
    pub(super) fn add_candmodel_construct_r15(&mut self) -> Result<(), SpecError> {
        for item in r15_items() {
            match item {
                R15Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R15Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r15_tests.rs"]
mod tests;
