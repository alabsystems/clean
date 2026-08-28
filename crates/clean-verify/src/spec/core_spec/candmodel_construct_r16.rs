// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R16 of the candidate-model construction ladder — **`sval` DERIVATION
//! IRRELEVANCE**, and the two payoffs R15 proved it was the only ingredient of.
//!
//! ## Why this rung
//!
//! R15 closed with a boundary stated as a kernel-checked constant rather than as
//! prose. `r15_val_conv_from_irrel` proves that `val_conv` follows from
//!
//! > `forall (h1 h2 : WK D e s) r, sval D e s h1 r = sval D e s h2 r`
//!
//! and from nothing else — confluence is NOT additionally needed for the
//! joinable form. The ∀-form of `val_step` sits behind the same one gap. This
//! rung discharges it.
//!
//! ## A — what landed, and why the route is SHORTER than the one R15 wrote down
//!
//! R15's handoff proposed *"`sval`-valued inversions at all five `WK` heads plus
//! `r15_wk_shape_unique`"*. Landing shape uniqueness FIRST makes a strictly
//! stronger and much cheaper statement reachable:
//!
//! * **`r16_wk_deriv_unique` — `WK` IS A SUBSINGLETON.** Any two derivations of
//!   the same term at the same shape are EQUAL. Shape assignment is
//!   syntax-directed (`WK` has no conversion rule) and its shapes are unique, so
//!   the derivation is determined by the term — proved here, not asserted.
//! * **`r16_sval_irrel` is then ONE `Eq.cong`.** The five semantic inversions
//!   R15 budgeted for collapse to a single DERIVATION inversion, and R13's
//!   funext and R14's `sval` congruences are not needed at all.
//!
//! The supporting pieces, each doing exactly one job:
//!
//! * **`r16_shapeOf` / `r16_shape_correct` / `r16_wk_shape_unique`** — the shape
//!   a term must have is COMPUTED by recursion on the term, every derivation
//!   agrees with it, and uniqueness is one `Eq.trans`. `Sk.arr`'s second-component
//!   injectivity (the `app` arm) is one `Eq.cong` through the computed
//!   `r16_arrCod`; no discrimination lemma appears anywhere, which is R15's
//!   computed-motive discipline carried forward.
//! * **`r16_wkT` / `r16_wk_inv`** — the one inversion, as a computed motive: a
//!   `KExpr.rec` on the SUBJECT sending each head to the CPS case analysis its
//!   `WK` rule deserves and `const`/`let_`/`proj`/`lit` to `r16_propUnit`, so
//!   those four arms die by COMPUTATION. Every live arm hands its own
//!   constructor fields to the continuation with `Eq.refl`, and the reflexive
//!   shape cast computes away by plain ι — **the inversion itself uses no K**.
//! * **`r16_pi_align` / `r16_lam_align` / `r16_app_align`** — the inversion
//!   returns subderivations at THEIR shapes; the induction hypothesis applies at
//!   the subject's. A based path induction (`Eq.rec`, Martin-Löf J) on each shape
//!   equation moves one onto the other. `app` needs only ONE J and NO cast at
//!   all, because `WK.app` carries the codomain shape as a bare index.
//!
//! ## The single K step, isolated
//!
//! After the J's, the leftover shape equation is REFLEXIVE but is a *variable*
//! proof, so plain ι does not fire. `Eq` is K-like in this kernel
//! (`env/inductive_recursor.rs::is_k_like`, exercised by
//! `tc/tests/recursor.rs::test_k_axiom_reduction`), so the kernel reduces the
//! major to `Eq.refl` and the cast computes away. That is the WHOLE of the
//! rung's reliance on it, and it is quarantined in one constant —
//! **`r16_wkCastS_refl`** — never inlined as a recursor minor. K is a kernel
//! reduction rule, not an axiom: `computed_axiom_closure` is empty for every
//! headline constant, and `test_candmodel_r16_k_step_is_load_bearing` measures
//! that the constant is doing real work rather than restating `Eq.refl`.
//!
//! ## B — the payoff
//!
//! * **`r16_val_conv`** — `val_conv`, UNCONDITIONALLY: two shape-typed terms
//!   with a common reduct have the same membership. R15's conditional with its
//!   hypothesis discharged.
//! * **`r16_val_step` / `r16_val_step_star`** — the ∀-form of `val_step`: the
//!   reduct's interpretation at an ARBITRARY derivation of the reduct agrees
//!   with the subject's, over one step and over a whole `whnfStar` sequence.
//!   This is R15's obstruction 2, closed. `PropBox` is the one piece of new
//!   machinery it needs: R15's fused theorems quantify their continuation over
//!   `C : Type`, the conclusion here is an `Eq` — a **Prop** — and the kernel is
//!   non-cumulative.
//! * **`r16_conv_contrast`** — R11's refutation of conversion-invariance for
//!   `candInterp` paired with UNCONDITIONAL conversion-invariance for `sval`, in
//!   one kernel-checked constant. The pair it is stated at converts WITHOUT
//!   either side reducing to the other (`r12_betaRedex` and `r16_convRedex2`,
//!   which share the contractum `instantiate (bvar 0) (sort 0)`) — R14's
//!   contrast was a head-β redex and R15's a single congruence step; this is the
//!   first that is a CONVERSION rather than a reduction.
//!
//! ## Does a genuinely different second derivation exist? NO — and that is proved
//!
//! The rung answers R15's open question mechanically rather than by inspection:
//! `r16_wk_deriv_unique` says no two derivations of one term at one shape can
//! differ. So irrelevance is *semantically* trivial and *definitionally* is not:
//! `r16_deriv_unique_witness` equates two derivation TERMS built by genuinely
//! different routes (R14's `wk_inst` and R15's `wk_step` run through the whole
//! computed step inversion), and `r16_irrel_witness` applies irrelevance at a
//! derivation the kernel CANNOT unfold at all — `r15_wk_step_sort` is registered
//! as a theorem, hence `Opaque`. The paired refusal test measures that the same
//! equation is NOT provable by `Eq.refl`, so the witness is not definitional in
//! disguise.
//!
//! ## What is untouched
//!
//! * **R10's `cr3` refutation and R11's `candInterp` conversion refutation
//!   stand.** `r16_conv_contrast` RE-ASSERTS R11 rather than repairing it: the
//!   positive result is conversion-invariance for **`sval`**, a different
//!   interpretation, on shape-typed terms only.
//! * **R12's TWO HORNS stand** — HORN 1 (predicativity) and HORN 2 (the
//!   derivation-indexed clause is not structural). Derivation irrelevance is
//!   neither, exactly as extensionality (R13), substitution (R14) and subject
//!   reduction (R15) were neither.
//! * **No SN capstone, and `sval` is still PARTIAL.** `WK` types five of
//!   `KExpr`'s nine constructors. Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## What still separates `WK` from `TypingCtx`, updated
//!
//! R15's list minus the item this rung closes. `WK` still has five constructors
//! against `KExpr`'s NINE (no `const`, `let_`, `proj`, `lit`); it still has **no
//! conversion rule**, so shape assignment is syntax-directed — and this rung
//! turns that from a caveat into a THEOREM, since it is exactly why `WK` is a
//! subsingleton and exactly what `TypingCtx` is not; its context is `Nat -> Sk`
//! — shapes, not types — and `piShape` still erases the codomain's dependence;
//! levels are still semantically inert; `sval` is still partial where a
//! `CandModel` law quantifies over all untyped `KExpr`; and there is still no SN
//! capstone from `WK` alone. **No longer on the list:** `sval` DERIVATION
//! IRRELEVANCE, and with it the ∀-form of `val_step` and `val_conv` — R15's
//! single named gap.
//!
//! ## Census
//!
//! ZERO new axioms. 38 constants — one inductive (`PropBox`), 13
//! `add_recursive_def` and 24 value-bearing theorems through `add_definition`
//! with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r16_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R15's theorem helper, verbatim: one `add_definition` per theorem so the
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

/// `(dependencies, description)` for every R16 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
#[allow(clippy::too_many_lines)]
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r16_propUnit" | "r16_propTriv" => (
            &["Eq", "Eq.refl", "Nat"],
            "THE PROP UNIT. The fragment has no Unit/True (whnf_progress.rs:143) and R15's \
             ConstFreeUnit is Type-sorted, so it cannot be the dead arm of a computed motive whose \
             live arms are Props — the kernel is NON-CUMULATIVE. A reflexive Eq is the cheapest \
             inhabited Prop the fragment already has, and it is what lets the four \
             const/let_/proj/lit arms of r16_wkT die by COMPUTATION.",
        ),
        "r16_arrCod" => (
            &["Sk.rec"],
            "The codomain of an arrow shape, junk elsewhere. One Eq.cong through it IS Sk.arr's \
             second-component injectivity — the app arm of r16_shape_correct — with no \
             discrimination lemma anywhere.",
        ),
        "PropBox" | "r16_propBox_intro" | "r16_unbox" => (
            &["Eq"],
            "THE PROP-TO-TYPE BRIDGE. R15's r15_val_step_sem / r15_val_star_sem quantify their \
             continuation over C : Type; the forall-form of val_step concludes an Eq, which is a \
             Prop, and the kernel is non-cumulative, so the Prop cannot be handed to them \
             directly. One one-field inductive closes it; nothing else in the rung needs it.",
        ),
        "r16_shapeOf" => (
            &["KExpr.rec", "domSk", "piShape", "skcons", "r16_arrCod"],
            "THE SHAPE A TERM MUST HAVE, computed by recursion on the TERM. The motive is KExpr -> \
             (Nat -> Sk) -> Sk rather than KExpr -> Sk because the environment changes under a \
             binder. This is what makes shape uniqueness four lines an arm instead of five CPS \
             inversions.",
        ),
        "r16_shape_correct" => (
            &["WK.rec", "r16_shapeOf", "Eq.cong", "Eq.substType", "Eq.trans"],
            "Every WK derivation agrees with the computed shape. var/sort are Eq.refl; pi/lam \
             chain two Eq.congs with one Eq.substType that moves the codomain's IH across the \
             domain shape it is indexed by; app is ONE Eq.cong through r16_arrCod.",
        ),
        "r16_wk_shape_unique" => (
            &["r16_shape_correct", "Eq.trans", "Eq.symm"],
            "SHAPE UNIQUENESS — the prerequisite R15 named. Two derivations of one term give the \
             same shape, because both agree with the computed one. One Eq.trans.",
        ),
        "r16_wkCastS" => (
            &["Eq.rec", "WK"],
            "Transport of a shape derivation along a shape equality. A def over a BARE Eq.rec, \
             because R14 measured that Eq.substType does not delta-unfold and a transport spelled \
             with it is opaque, so the Eq.refl base case never reduces.",
        ),
        "r16_wkCastS_refl" => (
            &["r16_wkCastS", "Eq.refl"],
            "THE RUNG'S ONE K STEP, QUARANTINED. After the based path inductions the leftover \
             shape equation is reflexive but is a VARIABLE proof, so plain iota does not fire. Eq \
             is K-like in this kernel (env/inductive_recursor.rs::is_k_like, exercised by \
             tc/tests/recursor.rs::test_k_axiom_reduction), so the kernel reduces the major to \
             Eq.refl and the cast computes away. K is a kernel REDUCTION RULE, not an axiom — the \
             computed axiom closure of every headline constant is empty. Standalone, never an \
             inlined recursor minor.",
        ),
        "r16_wkT" => (
            &["KExpr.rec", "WK", "r16_wkCastS", "r16_propUnit"],
            "THE COMPUTED DERIVATION INVERSION, as a type. A KExpr.rec on the SUBJECT sending each \
             head to the CPS case analysis its WK rule deserves and const/let_/proj/lit to \
             r16_propUnit, so those four arms discharge by COMPUTATION rather than by a \
             discrimination lemma. R15's r15_stepT idiom at the derivation rather than at the \
             step. Note the app clause needs NO shape cast: WK.app carries the codomain shape as a \
             bare index.",
        ),
        "r16_wk_inv" => (
            &["WK.rec", "r16_wkT", "Eq.refl"],
            "That inversion, proved by WK.rec. Every live arm hands its own constructor fields to \
             the continuation with Eq.refl, and the reflexive shape cast computes away by plain \
             iota — THE INVERSION ITSELF USES NO K. Registered as a def so its CPS result type \
             reduces at every call site.",
        ),
        "r16_uniq_var" | "r16_uniq_sort" => (
            &["r16_wk_inv", "r16_wkCastS_refl", "Eq.trans", "Eq.symm"],
            "The leaf arms of derivation uniqueness: no subderivations, so the whole content is \
             the inversion plus the cast-kill.",
        ),
        "r16_pi_align" | "r16_lam_align" => (
            &["Eq.rec", "r16_wk_shape_unique", "r16_wkCastS_refl", "Eq.cong"],
            "THE ALIGNMENT. The inversion returns subderivations at THEIR shapes; the induction \
             hypothesis applies at the subject's. Two based path inductions (Eq.rec, Martin-Lof J) \
             on the shape equations move one onto the other, after which the leftover cast is \
             reflexive and r16_wkCastS_refl kills it; two Eq.congs then rebuild the constructor \
             from the two IHs.",
        ),
        "r16_app_align" => (
            &["Eq.rec", "r16_wk_shape_unique", "Eq.cong"],
            "The cheapest alignment: ONE J and NO cast at all, because WK.app's conclusion carries \
             the codomain shape as a bare index, so only the DOMAIN shape has to be aligned. This \
             arm does not use K.",
        ),
        "r16_uniq_pi" | "r16_uniq_lam" | "r16_uniq_app" => (
            &["r16_wk_inv", "Eq.trans", "Eq.symm"],
            "The three structural arms: invert the second derivation, align it, compose. Note the \
             lam arm consumes BOTH induction hypotheses — the annotation's derivation is a FIELD \
             of WK.lam, so unlike r15_val_step_lamA (where the annotation is semantically inert) \
             it takes part here. Derivation equality is finer than semantic equality.",
        ),
        "r16_wk_deriv_unique" => (
            &[
                "WK.rec",
                "r16_uniq_var",
                "r16_uniq_sort",
                "r16_uniq_pi",
                "r16_uniq_lam",
                "r16_uniq_app",
            ],
            "WK IS A SUBSINGLETON — the rung's real result and strictly stronger than what R15 \
             asked for. Any two derivations of the same term at the same shape are EQUAL, because \
             shape assignment is syntax-directed (WK has no conversion rule) and its shapes are \
             unique. This also ANSWERS R15's open question mechanically: two genuinely different \
             derivations of one term cannot exist.",
        ),
        "r16_sval_irrel" => (
            &["Eq.cong", "r16_wk_deriv_unique", "sval"],
            "SVAL DERIVATION IRRELEVANCE — the constant this rung exists for, and exactly the \
             hypothesis r15_val_conv_from_irrel names. Given the subsingleton theorem it is ONE \
             Eq.cong, which is why the five semantic inversions R15 budgeted for were not needed.",
        ),
        "r16_val_conv" => (
            &["r15_val_conv_from_irrel", "r16_sval_irrel"],
            "VAL_CONV, UNCONDITIONALLY. R15's conditional with its hypothesis discharged: two \
             shape-typed terms with a COMMON REDUCT have the same membership. Confluence is not \
             additionally needed for this joinable form — R15 proved that, and this rung supplies \
             the one thing it was waiting on.",
        ),
        "r16_val_step" | "r16_val_step_star" => (
            &["r15_val_step_sem", "r15_val_star_sem", "r16_sval_irrel", "r16_unbox"],
            "THE FORALL-FORM OF VAL_STEP — R15's obstruction 2, closed. R15 could only produce SOME \
             derivation of the reduct whose interpretation agreed; irrelevance moves that to an \
             ARBITRARY one, over one step and over a whole whnfStar sequence. PropBox is the \
             non-cumulativity bridge: R15's fused theorems quantify over C : Type and this \
             conclusion is a Prop.",
        ),
        "r16_convRedex2" | "r16_convDeriv2" | "r16_convStep2" | "r16_convStar1"
        | "r16_convStar2" => (
            &["WK.app", "WK.lam", "whnfStar.step", "beta_reduces.beta"],
            "THE SECOND REDEX AND THE JOIN. `(fun (x : bvar 1). x) (Sort 0)` — every slot of \
             r12_betaEnv is kd (kd ty), so bvar 1 annotates exactly as bvar 0 does. Both redexes \
             contract to instantiate (bvar 0) (sort 0) and NEITHER reduces to the other, so the \
             contrast below is a genuine CONVERSION rather than a reduction.",
        ),
        "r16_svalConvTransports" => (
            &["vcarD", "sval", "r12_betaDeriv", "r16_convDeriv2"],
            "The membership transport across that conversion, as a named Type so it can sit inside \
             an AndType beside R11's refutation. CONCRETE for R15's measured universe reason: any \
             generic statement here quantifies over a valuation, VEnvD D is Type 1, and a def : \
             Type carrying one is refused with \"expected Type, got Type 1\".",
        ),
        "r16_sval_conv_transports" => (
            &["r16_val_conv", "r16_convStar1", "r16_convStar2"],
            "That transport, PROVED — r16_val_conv at the concrete join.",
        ),
        "r16_conv_contrast" => (
            &[
                "AndType.intro",
                "r11_candInterp_step_conv_refuted",
                "r16_sval_conv_transports",
            ],
            "R12's / R15's contrast pattern one rung on, and the strongest form the ladder has \
             reached: R11's refutation of conversion-invariance for candInterp paired with \
             UNCONDITIONAL conversion-invariance for sval, in ONE kernel-checked constant. It \
             RE-ASSERTS R11 rather than repairing it — the positive half is about a different \
             interpretation, on shape-typed terms only.",
        ),
        "r16_shape_unique_witness" => (
            &["r16_wk_shape_unique", "r15_instDeriv", "r15_wk_step_witness"],
            "Shape uniqueness at two derivation TERMS of one term built by different routes: R14's \
             wk_inst and R15's wk_step.",
        ),
        "r16_deriv_unique_witness" => (
            &["r16_wk_deriv_unique", "r15_instDeriv", "r15_wk_step_witness"],
            "NON-VACUITY at two genuinely different derivation TERMS. r15_instDeriv is built by \
             R14's wk_inst out of WK.var / WK.sort; r15_wk_step_witness is R15's wk_step run on \
             r12_betaDeriv through the whole computed step inversion. This constant proves them \
             EQUAL.",
        ),
        "r16_irrel_witness" => (
            &["r16_sval_irrel", "r15_wk_step_sort"],
            "Irrelevance at a derivation the kernel CANNOT unfold: r15_wk_step_sort is registered \
             as a theorem, hence Opaque, so sval at it is stuck. The paired refusal test measures \
             that the same equation is NOT provable by Eq.refl, so the witness is not definitional \
             in disguise.",
        ),
        "r16_val_step_witness" => (
            &["r16_val_step", "r12_betaDeriv", "r15_instDeriv"],
            "The forall-form of val_step COMPUTED at R12's registered redex, at r15_instDeriv — a \
             derivation of the reduct that r15_val_step_sem never produced.",
        ),
        _ => (&[], "R16 sval derivation irrelevance."),
    }
}

impl Specification {
    /// Register R16: `sval` derivation irrelevance and its two payoffs.
    pub(super) fn add_candmodel_construct_r16(&mut self) -> Result<(), SpecError> {
        for item in r16_items() {
            match item {
                R16Item::Ind { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_inductive(&src, desc)?;
                }
                R16Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R16Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r16_tests.rs"]
mod tests;
