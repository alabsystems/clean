// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R17 of the candidate-model construction ladder — **THE CONSTRUCTOR GAP**:
//! `const` and `let_` land on the `WK`/`sval` lineage, with every operation
//! R14-R16 built extended to them, and the conversion-rule question SETTLED.
//!
//! ## Why this rung
//!
//! R16 closed with a verdict rather than a handoff:
//!
//! > *"the next question is the four missing constructors and the conversion
//! > rule themselves, not another `WK` metatheorem."*
//!
//! Two lineages had been running, each strong where the other was weak. The
//! `SynTy*` lineage (R6-R11) over `candInterp` had broad constructor coverage —
//! including a `const` rule at any type — but `candInterp` is PROVED not
//! conversion-invariant (R11). The `WK`/`sval` lineage (R12-R16) had the whole
//! metatheory — weakening, substitution, instantiation, subject reduction,
//! derivation irrelevance, `val_conv` unconditionally — over five constructors
//! and no `const`, no `let_`. This rung moves two of the four constructors onto
//! the lineage that has the metatheory, and carries the metatheory with them.
//!
//! ## A — the system, and the ONE design decision in each new rule
//!
//! `WKC : (Nat -> Sk) -> KExpr -> Sk -> Type` is R12's `WK` verbatim in its five
//! landed constructors plus:
//!
//! * **`konst`** — an INERT constant is shape-typed at `Sk.ty`. "Inert" is
//!   R10's pair of side conditions, spelled as R10 spells them: `defval_for
//!   (red_def the_red_env) n = none` and `recmeta_for (red_rec the_red_env) n =
//!   none`.
//!
//!   **Which of the two honest options this is, and why.** The task offered a
//!   shape environment for constants (`Name -> Sk`, a `const` at any shape) or
//!   the inert case only. The inert case is chosen and the choice is PROVED
//!   rather than argued: **`r17_unrestricted_konst_refuted`** pairs a REAL δ
//!   step out of a REAL reflected constant (`the_red_env_delta_nonvacuous`,
//!   whose target is a `lam` — R9's finding that every real body in
//!   `the_red_env` is one) with **`r17_lam_never_ty`**, the proof that no `lam`
//!   can carry `Sk.ty`. A `Sk.ty`-valued rule at a δ-active constant therefore
//!   loses subject reduction outright. The alternative — a `Name -> Sk`
//!   environment — is not refuted by this; what is refuted is the cheap version
//!   of it, and the honest reading is that the general rule needs a SOUNDNESS
//!   condition tying the constant environment to `the_red_env`'s bodies, which
//!   is a rung of its own.
//!
//!   The premises are `Eq`s, hence **Props**, and that is load-bearing: the
//!   kernel's definitional proof irrelevance is what makes `r17_uniq_konst` the
//!   cast-kill plus ONE application of `r17_konst_irrel`. Had the rule carried
//!   R10's `Type`-valued `HeadInert` instead, the subsingleton would have failed
//!   at that arm. R14's position dependence recurred verbatim and is recorded:
//!   the irrelevance step had to be factored into its own `add_recursive_def`
//!   constant, because written inline the ELABORATOR compares the two proof
//!   binders as free variables and refuses (`fvar mismatch: FVarId(7) vs
//!   FVarId(3)`, measured on this rung's first cycle).
//!
//! * **`let_`** — three premises (annotation, value, body) and **the binder slot
//!   carries the shape of the VALUE**, not of the annotation. That is the whole
//!   design: it makes ζ subject reduction land on `wkc_inst` exactly as head-β
//!   does, and it makes the semantic ζ law definitional.
//!
//! `xval` is the seven-clause interpretation. `konst` denotes the TOP candidate
//! (sound because an inert constant admits NO `whnf_step` at all —
//! `r17_const_no_step`); `let_` denotes the body at the valuation EXTENDED BY
//! THE VALUE'S.
//!
//! **`r17_xval_zeta` is `Eq.refl`, and that OVERTURNS the transfer of R1's
//! refutation.** R1 refuted the generic per-set ζ engine, and R8 landed only a
//! sort-annotated ζ fragment on the other lineage. Neither verdict binds here,
//! and the reason is structural, not effort: R1's refutation is about candidate
//! SETS closing under ζ-expansion for an ARBITRARY `S`; `xval` is an
//! INTERPRETATION that reads a valuation, so the `let_` clause is a valuation
//! extension and the ζ law is the `lam`/`app` pair's law with the argument
//! supplied — exactly R12's `r12_sval_beta`, one constructor over. R8's
//! `r8_zeta_obstruction_located` named the general case's missing ingredient on
//! the `candInterp` lineage; on this one it is not missing.
//!
//! ## B — every landed operation, extended
//!
//! * **`wkc_lift` / `wkc_lift0` / `wkc_up` / `wkc_psub` / `wkc_inst`** — R14's
//!   five, at seven constructors. Both new arms are cheap and for the same
//!   reason: `lift_at` and `psubst` leave a `const` alone outright and treat a
//!   `let_` exactly as a `lam`, so R14's recursive `skins` keeps the `let_`
//!   binder case transport-free too.
//! * **`wkc_step`** — subject reduction, total and unconditional.
//! * **`r17_shape_correct` / `r17_wkc_shape_unique`** — R16's shape uniqueness.
//!   `r17_shapeOf` is R16's with two junk arms replaced; the `const` arm did not
//!   have to move, since R16's junk value there was already `Sk.ty`.
//! * **`r17_wkc_deriv_unique` — THE SUBSINGLETON SURVIVES.** Any two `WKC`
//!   derivations of one term at one shape are EQUAL, and therefore
//!   `r17_xval_irrel` is still ONE `Eq.cong`.
//!
//! **Why the subsingleton survives, stated precisely.** R16's proof works
//! because shape assignment is syntax-directed. Both new rules preserve that:
//! each is keyed by the subject's head constructor, neither is optional, and
//! neither introduces a choice. `konst`'s only freedom is in **Prop** (killed by
//! proof irrelevance); `let_`'s two existential shapes `st`/`sv` are pinned by
//! `r17_wkc_shape_unique` exactly as `lam`'s `sA` and `app`'s `d` are.
//! `r17_deriv_unique_witness` is the non-vacuity check, at two derivation TERMS
//! of one judgment built by genuinely different routes — R14's `wk_inst` pushed
//! through the embedding, and this rung's `wkc_step` run on the ζ redex through
//! the whole `letRedex_whnf_inv`.
//!
//! ## THE STRUCTURAL FACT that kept subject reduction cheap
//!
//! Adding `const` re-opens δ and ι, which R15 had closed by proving `WK` never
//! types a const-headed spine (`r15_headFree_wk`). The replacement is
//! **`r17_headFree_wkc_arr`: `WKC` never types a const-headed spine AT AN ARROW
//! SHAPE** — `WKC.konst` concludes at `Sk.ty` and at no other shape, and
//! `WKC.app`'s function premise is exactly at an arrow shape. FIVE of its seven
//! arms are one token (`var`/`sort`/`pi`/`lam`/`let_` are head-free outright),
//! the `app` arm is `headFree_app` at its own induction hypothesis, and the
//! `konst` arm dies by COMPUTATION through the `Sk` discriminator
//! `r17_notArrT`.
//!
//! Consequence, and it is the rung's cheapest surprise: **R15's
//! `r15_whnf_stepT_inv` is consumed VERBATIM in five of `wkc_step`'s seven
//! arms**, and R10's `HeadInert` inversion machinery — which looked like the
//! obvious prerequisite — is not needed by subject reduction at all. The
//! `konst` arm is a refutation (`r17_const_no_step`, off R2's
//! `constRedex_whnf_inv` and R10's δ arm) and the `let_` arm is R1's
//! `letRedex_whnf_inv`.
//!
//! `r17_headInert_wkc` is registered anyway, because it is where the `konst`
//! rule's SECOND premise earns its place: subject reduction needs only
//! `defval_for = none`, and `inertConst_headInert` needs both. R10's interface
//! is therefore supplied for the whole extended system.
//!
//! ## C — the conversion rule, SETTLED (and deliberately NOT built)
//!
//! R16's subsingleton holds *precisely because* `WK` has no conversion rule, and
//! `TypingCtx` has one. The question is answered on the smallest system that
//! exhibits it — `WKV`, two leaf rules plus `conv` at the FINEST possible shape
//! relation, propositional equality:
//!
//! * **`r17_conv_shape_unique` — shape assignment SURVIVES.** Shapes are
//!   determined by the term through `r17_shapeOf`, and a conversion rule can
//!   only move a shape to one it is already equal to. The `conv` arm is one
//!   `Eq.trans`.
//! * **`r17_conv_breaks_subsingleton` — derivation uniqueness does NOT.**
//!   `WKV.var D i` and the identity conversion applied to it derive the SAME
//!   judgment and are provably DISTINCT. Note where this lands: at `Eq Sk`, the
//!   finest relation there is, so it is not an artefact of a coarse conversion
//!   and no weakening of the relation rescues it.
//! * **`r17_conv_verdict`** pairs the two in one kernel-checked constant.
//!
//! **The consequence for irrelevance, stated honestly.** Losing the
//! subsingleton does not by itself lose `xval` irrelevance — a `conv` clause
//! interpreted by a `VD` transport is semantically inert at a reflexive proof —
//! but it does lose R16's ONE-LINE route to it, and irrelevance would have to
//! be re-proved through the five `sval`-valued head inversions R15 originally
//! budgeted for. That is why this rung does not build a conversion rule into
//! `WKC`: the task's instruction was to determine the answer and only build if
//! it is safe. It is not safe for the proof that R16's payoffs rest on.
//!
//! ## What did NOT land, and why — read before quoting
//!
//! * **`proj` and `lit` are still untyped, and this rung does not claim them.**
//!   `r17_wkcT`'s dead-arm count drops from four to two, and those two are what
//!   is left. They are the case the task flagged as possibly needing type
//!   information shapes erase — `proj s i sub` reads the `i`-th field of a
//!   structure, and `Sk` records neither field count nor field shapes — and
//!   nothing here proves or refutes it.
//! * **No `xval`-side re-derivation of R14/R15's SEMANTIC lemmas.**
//!   `r17_xval_irrel` is the derivation-irrelevance theorem; `val_lift`,
//!   `val_psub`, `val_step_sem`, `val_star_sem` and `val_conv` are stated and
//!   proved for **`sval`** in R14-R16 and are NOT restated for `xval`. What
//!   transfers today is the embedding `r17_wk_wkc` and the shape-level
//!   agreement `r17_shapeOf_agrees_on_wk`; the semantic transfer
//!   (`xval (wk_wkc h) r = sval h r`) is the named next item.
//! * **R10's `cr3` refutation, R11's `candInterp` conversion refutation and
//!   R12's TWO HORNS are untouched and still stand.** Nothing here is about
//!   `candInterp`, and the constructor gap is neither a universe obstruction
//!   nor a structural-recursion one.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## What still separates `WKC` from `TypingCtx`, updated
//!
//! R16's list minus what this rung closes. `WKC` has SEVEN constructors against
//! `KExpr`'s nine — **no `proj`, no `lit`**; it still has no conversion rule,
//! and this rung turns that from a caveat into a MEASURED TRADE (shape
//! uniqueness would survive, derivation uniqueness would not); its context is
//! `Nat -> Sk` — shapes, not types — and `piShape` still erases the codomain's
//! dependence; levels are still semantically inert; `konst` is restricted to
//! INERT constants where `TypingCtx.const` reads a declared type off a `tenv`,
//! and closing that needs a constant shape environment plus a soundness
//! condition against `the_red_env`; `xval` is still partial where a `CandModel`
//! law quantifies over all untyped `KExpr`; and there is still no SN capstone.
//! **No longer on the list:** `const` and `let_` themselves, and the whole
//! weakening / substitution / instantiation / subject-reduction / shape-
//! uniqueness / derivation-uniqueness / interpretation-irrelevance stack over
//! them.
//!
//! ## Census
//!
//! ZERO new axioms. 62 constants — two inductives (`WKC` and the conversion
//! probe `WKV`; `PropBox` is R16's, reused), 29 `add_recursive_def` and 31
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking. `computed_axiom_closure` is empty for every headline constant:
//! definitional proof irrelevance and K-like reduction are kernel REDUCTION
//! RULES, not axioms.

use std::collections::HashSet;

// Part 1's names are consumed by the `#[path]`-included test module below,
// which resolves them through `use super::*`.
#[allow(unused_imports)]
use super::candmodel_construct_r17_src::*;
use super::candmodel_construct_r17_src2::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R16's theorem helper, verbatim: one `add_definition` per theorem so the
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

/// `(dependencies, description)` for every R17 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
#[allow(clippy::too_many_lines)]
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "WKC" => (
            &["Sk", "KExpr", "skcons", "domSk", "piShape", "defval_for", "recmeta_for"],
            "SHAPE TYPING WITH CONSTANTS AND LET. R12's WK verbatim in its five landed \
             constructors plus konst (an INERT constant — R10's two side conditions, spelled as \
             Eq's so proof irrelevance keeps the system a subsingleton — at Sk.ty) and let_ (three \
             premises, binder slot carrying the shape of the VALUE, which is what makes zeta \
             subject reduction land on wkc_inst exactly as head-beta does). Every constructor \
             leads with D and every recursive premise changes it, so fixedIndicesToParams cannot \
             fire and WKC.rec takes D after its minors, exactly as WK.rec does.",
        ),
        "xval" => (
            &["WKC.rec", "VD", "VEnvD", "vconsD", "mkTyD", "PiSet", "vcarD", "junkD", "whnf_acc"],
            "THE SEVEN-CLAUSE INTERPRETATION. R12's sval clauses plus: konst denotes the TOP \
             candidate (sound because an inert constant admits NO whnf_step — r17_const_no_step, \
             so nothing ever has to agree with a body), and let_ denotes the body at the valuation \
             EXTENDED BY THE VALUE'S. The second is why r17_xval_zeta is Eq.refl.",
        ),
        "r17_wk_wkc" => (
            &["WK.rec", "WKC"],
            "THE EMBEDDING. Every WK derivation is a WKC derivation — the extension adds \
             constructors and removes none, so R12-R16's whole lineage survives inside this one. A \
             def, so later proofs reduce through it.",
        ),
        "r17_notArrT" => (
            &["Sk.rec", "ConstFreeUnit", "Empty"],
            "The Sk discriminator, COMPUTED: ConstFreeUnit off the arrows, Empty at one. Feeding a \
             shape equation through it IS the discrimination — R16's discipline, no hand-written \
             ne-lemma anywhere in the rung.",
        ),
        "r17_shapeOf" => (
            &["KExpr.rec", "domSk", "piShape", "skcons", "r16_arrCod"],
            "THE SHAPE A TERM MUST HAVE, at NINE heads. R16's r16_shapeOf with two junk arms \
             replaced by real ones. The const arm did NOT have to move: R16's junk value there was \
             already Sk.ty, which is exactly what WKC.konst concludes. The let_ arm is the body's \
             shape in the environment extended by the VALUE's — the arm R16 had no rule for.",
        ),
        "r17_shape_correct" => (
            &["WKC.rec", "r17_shapeOf", "Eq.cong", "Eq.substType", "Eq.trans"],
            "Every WKC derivation agrees with the computed shape. The konst arm is Eq.refl; the \
             let_ arm is ONE Eq.substType and no Eq.trans at all, because the conclusion shape is a \
             bare index and the only work is moving the body's IH across the VALUE's shape.",
        ),
        "r17_wkc_shape_unique" => (
            &["r17_shape_correct", "Eq.trans", "Eq.symm"],
            "SHAPE UNIQUENESS at seven constructors. One Eq.trans, exactly as R16.",
        ),
        "r17_shapeOf_agrees_on_wk" => (
            &["r16_shape_correct", "r17_shape_correct", "r17_wk_wkc"],
            "CONSERVATIVITY, in one line: on every term the OLD system types, R16's shape function \
             and this rung's agree. Two shape-correctness theorems composed through the embedding.",
        ),
        "r17_lam_never_ty" => (
            &["r17_shape_correct", "r17_notArrT", "Eq.substType"],
            "A lam is shape-typed at an Sk.arr, NEVER at Sk.ty. The whole content of the \
             unrestricted-konst refutation, with no discrimination lemma: r17_shapeOf COMPUTES an \
             Sk.arr at a lam and r17_notArrT reads it.",
        ),
        "r17_wkcCastS" | "r17_wkcCastT" => (
            &["Eq.rec", "WKC"],
            "Transport of a WKC derivation along a shape / term equality. A def over a BARE Eq.rec, \
             because R14 measured that Eq.substType does not delta-unfold and a transport spelled \
             with it is opaque, so the Eq.refl base case never reduces.",
        ),
        "r17_wkcCastS_refl" => (
            &["r17_wkcCastS", "Eq.refl"],
            "THE RUNG'S ONE K STEP, QUARANTINED, exactly as R16's. After the based path inductions \
             the leftover shape equation is reflexive but is a VARIABLE proof, so plain iota does \
             not fire; Eq is K-like in this kernel, the major reduces to Eq.refl and the cast \
             computes away. K is a kernel REDUCTION RULE, not an axiom. Standalone, never an \
             inlined recursor minor.",
        ),
        "r17_wkcT" => (
            &["KExpr.rec", "WKC", "r17_wkcCastS", "r16_propUnit"],
            "THE COMPUTED DERIVATION INVERSION, as a type, at NINE heads of which SEVEN are now \
             live. Only proj and lit still die through r16_propUnit — the constructor gap made \
             machine-visible, dead arms 4 -> 2. The let_ clause needs NO shape cast (WKC.let_ \
             carries the conclusion shape as a bare index, like WKC.app); the konst clause hands \
             back both INERTNESS PROOFS.",
        ),
        "r17_wkc_inv" => (
            &["WKC.rec", "r17_wkcT", "Eq.refl"],
            "That inversion, proved by WKC.rec. Every live arm hands its OWN constructor fields to \
             the continuation with Eq.refl — the konst arm hands back its two inertness proofs the \
             same way, so no proof-irrelevance step happens here. Registered as a def so its CPS \
             result type reduces at every call site.",
        ),
        "r17_uniq_var" | "r17_uniq_sort" => (
            &["r17_wkc_inv", "r17_wkcCastS_refl", "Eq.trans", "Eq.symm"],
            "The leaf arms of derivation uniqueness: no subderivations, so the whole content is \
             the inversion plus the cast-kill.",
        ),
        "r17_konst_irrel" => (
            &["WKC.konst", "Eq.refl"],
            "THE PROOF-IRRELEVANCE STEP, AS A STANDALONE CONSTANT. Two konst derivations of one \
             judgment differ only in their INERTNESS PROOFS, which are Eq's and therefore Props, \
             and the KERNEL holds any two proofs of a Prop definitionally equal — so the statement \
             is Eq.refl. It MUST be its own constant, and that is measured: R14 recorded the \
             position dependence (r14_vdCast_irrel), and R17 hit it on its first cycle — written \
             inline in r17_uniq_konst the ELABORATOR compared the two proof binders as free \
             variables and refused with `fvar mismatch: FVarId(7) vs FVarId(3)`, while the \
             identical statement registers cleanly through add_recursive_def. Had the rule's \
             premises been the Type-valued HeadInert instead of R10's two Eq side conditions, no \
             factoring would have helped and the subsingleton would have been LOST.",
        ),
        "r17_uniq_konst" => (
            &["r17_wkc_inv", "r17_wkcCastS_refl", "r17_konst_irrel", "Eq.trans", "Eq.symm"],
            "The konst arm of derivation uniqueness: the inversion, the cast-kill, and ONE \
             application of the standalone irrelevance step. No J and no induction — konst has no \
             subderivations.",
        ),
        "r17_pi_align" | "r17_lam_align" => (
            &["Eq.rec", "r17_wkc_shape_unique", "r17_wkcCastS_refl", "Eq.cong"],
            "THE ALIGNMENT, R16's verbatim at WKC: two based path inductions move the inversion's \
             shapes onto the subject's, the leftover reflexive cast dies by K, and two Eq.congs \
             rebuild the constructor from the two IHs.",
        ),
        "r17_app_align" => (
            &["Eq.rec", "r17_wkc_shape_unique", "Eq.cong"],
            "ONE J and NO cast: WKC.app's conclusion carries the codomain shape as a bare index, so \
             only the DOMAIN shape has to be aligned. This arm does not use K.",
        ),
        "r17_let_align" => (
            &["Eq.rec", "r17_wkc_shape_unique", "Eq.cong", "Eq.trans"],
            "THE NEW ALIGNMENT. Like app, WKC.let_ carries the conclusion shape as a bare index, so \
             there is NO CAST and no K step. What it does have is TWO existential shapes — the \
             annotation's and the VALUE's — so two J's where app needs one, and three Eq.congs \
             where app needs two.",
        ),
        "r17_uniq_pi" | "r17_uniq_lam" | "r17_uniq_app" | "r17_uniq_let" => (
            &["r17_wkc_inv", "Eq.trans", "Eq.symm"],
            "The structural arms: invert the second derivation, align it, compose. The let_ arm \
             consumes all THREE induction hypotheses — the annotation's derivation is a field of \
             WKC.let_ even though the annotation is semantically inert, because derivation \
             equality is finer than semantic equality.",
        ),
        "r17_wkc_deriv_unique" => (
            &[
                "WKC.rec",
                "r17_uniq_var",
                "r17_uniq_sort",
                "r17_uniq_pi",
                "r17_uniq_lam",
                "r17_uniq_app",
                "r17_uniq_konst",
                "r17_uniq_let",
            ],
            "THE SUBSINGLETON SURVIVES THE EXTENSION. R16's headline at seven constructors: any \
             two WKC derivations of one term at one shape are EQUAL. It survives because both new \
             rules preserve syntax-directedness — each is keyed by the subject's head constructor, \
             neither is optional, konst's only freedom is in Prop, and let_'s two existential \
             shapes are pinned by shape uniqueness exactly as lam's sA and app's d are.",
        ),
        "r17_xval_irrel" => (
            &["Eq.cong", "r17_wkc_deriv_unique", "xval"],
            "XVAL DERIVATION IRRELEVANCE — still ONE Eq.cong, because the subsingleton survived. \
             The constant that would have been lost if either new arm had introduced \
             non-determinism.",
        ),
        "r17_wkc_lift_var" => (
            &["r17_wkcCastT", "r17_wkcCastS", "r14_skins_idx", "r14_lift_at_bvar_wkpos", "WKC.var"],
            "The var leaf of weakening, and the only place in the operation group that needs a \
             transport — R14's two, at WKC. A def, because wkc_lift must REDUCE through it.",
        ),
        "wkc_lift" => (
            &["WKC.rec", "skins", "lift_at", "r17_wkc_lift_var"],
            "THE WEAKENING OPERATION at seven constructors. Both new arms are cheap for the same \
             reason: lift_at leaves a const alone outright, and treats a let_ exactly as a lam, so \
             R14's recursive skins keeps the let_ binder case transport-free too.",
        ),
        "wkc_lift0" => (
            &["wkc_lift", "skcons"],
            "Weakening at the HEAD of the shape environment; definitional at cutoff zero.",
        ),
        "wkc_up" => (
            &["wkc_lift0", "up", "scons", "WKC.var"],
            "The up-closure of a shape-typed substitution — the ONE place weakening enters \
             substitution, and why the two cannot be proved in either order alone.",
        ),
        "wkc_psub" => (
            &["WKC.rec", "psubst", "up", "wkc_up"],
            "THE SUBSTITUTION OPERATION at seven constructors. psubst leaves a const alone and \
             sends a let_ to (annotation, value) at the substitution and body under up, so both \
             new arms mirror the sort and lam ones exactly.",
        ),
        "r17_scons_typed" => (
            &["Nat.rec", "scons", "idsubst", "WKC.var"],
            "The single-slot substitution scons a idsubst, shape-typed. Transport-free.",
        ),
        "wkc_inst" => (
            &["wkc_psub", "r17_scons_typed", "instantiate_eq_psubst", "r17_wkcCastT"],
            "Substitution for the ZEROTH slot at the kernel's own instantiate. The contractum \
             derivation for BOTH head-beta and zeta.",
        ),
        "r17_headFree_wkc_arr" => (
            &["WKC.rec", "HeadFree", "headFree_app", "r17_notArrT", "Empty.rec"],
            "THE STRUCTURAL FACT that keeps subject reduction cheap. R15's r15_headFree_wk said WK \
             never types a const-headed spine; adding konst breaks that, and the replacement is \
             that WKC never types a const-headed spine AT AN ARROW SHAPE — WKC.konst concludes at \
             Sk.ty and nowhere else, and WKC.app's function premise is exactly at an arrow. FIVE \
             of seven arms are one token, the app arm is headFree_app at its own IH, and the konst \
             arm dies by COMPUTATION through r17_notArrT. \
             Consequence: R15's r15_whnf_stepT_inv is reused VERBATIM in five of wkc_step's seven \
             arms and R10's HeadInert inversion machinery is not needed by subject reduction at all.",
        ),
        "r17_headInert_wkc" => (
            &["WKC.rec", "HeadInert", "headInert_app", "inertConst_headInert"],
            "R10's interface, supplied for the whole extended system: every shape-typed term is \
             head-INERT. This is where the konst rule's SECOND premise (recmeta_for = none) earns \
             its place — subject reduction needs only defval_for = none, and inertConst_headInert \
             needs both.",
        ),
        "r17_const_no_step" => (
            &["constRedex_whnf_inv", "delta_reduct_eq_none_of_defval_none", "option_none_ne_some_type"],
            "AN INERT CONSTANT ADMITS NO whnf_step AT ALL. The beta leg is R2's \
             r2_const_no_beta_reduces through constRedex_whnf_inv (a bare const admits no \
             beta_reduces for ANY name — an empty spine has no major premise, so even the iota arm \
             dies unconditionally); the delta leg is R10's own delta arm at the head-name equation \
             a bare const satisfies by Eq.refl. Only defval_for = none is consumed, which is the \
             measured reason the recmeta premise is NOT needed by subject reduction.",
        ),
        "r17_wkcLamT" | "r17_wkc_lam_inv" => (
            &["KExpr.rec", "Sk.rec", "WKC.rec", "ConstFreeUnit"],
            "R15's WK-only lambda inversion at WKC: a KExpr.rec on the term nested with a Sk.rec on \
             the shape, every pair but (lam, arr) ConstFreeUnit. Two more dead arms than R15's \
             (nine heads, not five), all still one token. A def, because wkc_step must REDUCE \
             through it in its head-beta arm.",
        ),
        "wkc_step" => (
            &[
                "WKC.rec",
                "r15_whnf_stepT_inv",
                "letRedex_whnf_inv",
                "r17_const_no_step",
                "r17_wkc_lam_inv",
                "wkc_inst",
                "r17_wkcCastT",
                "r17_headFree_wkc_arr",
            ],
            "SUBJECT REDUCTION FOR SHAPES at seven constructors — total, unconditional, a def so a \
             later rung can reduce through it. Five arms reuse R15's step inversion verbatim. The \
             konst arm is a REFUTATION (no step exists). The let_ arm is R1's letRedex_whnf_inv, \
             and its zeta case lands on wkc_inst exactly as head-beta does — that is what the \
             let_ rule's value-shaped binder slot was chosen for. The let_val congruence needs no \
             re-indexing of the body for the same reason.",
        ),
        "WKV" => (
            &["Sk", "KExpr", "Eq"],
            "THE CONVERSION-RULE PROBE: the smallest system that exhibits the phenomenon — two \
             leaf rules plus conv at the FINEST possible shape relation, propositional equality. \
             Registered to SETTLE the question, not to be built on.",
        ),
        "r17_wkv_shape_correct" | "r17_conv_shape_unique" => (
            &["WKV.rec", "r17_shapeOf", "Eq.trans", "Eq.symm"],
            "SHAPE ASSIGNMENT SURVIVES A CONVERSION RULE. Shapes are determined by the term through \
             r17_shapeOf, and a conversion rule can only move a shape to one it is already equal \
             to, so the conv arm is one Eq.trans. Half of the settled answer.",
        ),
        "r17_wkv_tag" | "r17_zeroT" | "r17_convDeriv" => (
            &["WKV.rec", "Nat.rec", "ConstFreeUnit", "Empty"],
            "The discrimination apparatus: the constructor tag of a WKV derivation, the computed \
             Nat discriminator, and the SECOND derivation of a judgment that already has one — the \
             identity conversion applied to WKV.var. All defs, so the discrimination computes.",
        ),
        "r17_conv_breaks_subsingleton" => (
            &["r17_wkv_tag", "r17_zeroT", "r17_convDeriv", "Eq.cong", "Eq.substType"],
            "A CONVERSION RULE BREAKS THE SUBSINGLETON — PROVED, not conjectured. WKV.var D i and \
             the identity conversion applied to it derive the SAME judgment and are provably \
             DISTINCT, so R16's r16_wk_deriv_unique has no counterpart in any system with a \
             conversion rule. The refutation lands at Eq Sk, the FINEST relation there is, so it \
             is not an artefact of a coarse conversion and no weakening of the relation rescues \
             uniqueness. This is why the rung does not build conv into WKC.",
        ),
        "r17_conv_verdict" => (
            &["AndType.intro", "PropBox", "r17_conv_shape_unique", "r17_conv_breaks_subsingleton"],
            "The two halves in ONE kernel-checked constant, the ladder's contrast idiom: under a \
             conversion rule the SHAPE is still unique and the DERIVATION is not. PropBox is the \
             non-cumulativity bridge — the first half is a forall into Eq, hence a Prop, and \
             AndType takes Types.",
        ),
        "r17_konst_witness" => (
            &["WKC.konst", "r12_piEnv", "the_red_env"],
            "The konst rule at R9/R10's REAL reflected dead constant (kcre_name_12): both \
             inertness premises hold by Eq.refl over the live the_red_env. R9's \
             synTyC_konst_dead_witness and R11's r11_interp_const_pi_witness are the precedent; \
             this is the same constant, now shape-typed on the lineage that has the metatheory.",
        ),
        "r17_deadConst_acc" => (
            &["whnf_acc.intro", "r17_const_no_step"],
            "That constant is whnf_acc, through r17_const_no_step — the inert constant is stuck, \
             so the konst clause's TOP-candidate interpretation is not merely convenient.",
        ),
        "r17_konst_mem_witness" => (
            &["vcarD", "xval", "r17_konst_witness", "r17_deadConst_acc"],
            "NON-DEGENERACY of the konst interpretation clause: the constant is a MEMBER of the \
             candidate its own derivation denotes.",
        ),
        "r17_letTerm" | "r17_let_witness" => (
            &["WKC.let_", "r12_betaEnv", "KExpr.let_"],
            "R15's OWN let probe, made a theorem. probe_wk_step_at_let records that WK cannot even \
             STATE wk_step at let_ (sort 0) (sort 0) (bvar 0); WKC types it, at the shape \
             r17_shapeOf computes.",
        ),
        "r17_xval_zeta" => (
            &["xval", "WKC.let_", "vconsD", "Eq.refl"],
            "SEMANTIC ZETA IS DEFINITIONAL — the analogue of R12's r12_sval_beta, one constructor \
             over, and the settled answer to whether R1's refutation transfers. It does NOT: R1 \
             refuted the generic per-set zeta ENGINE, which must close an ARBITRARY candidate set \
             under zeta-expansion; xval is an INTERPRETATION that reads a valuation, so the let_ \
             clause is a valuation extension and the law is Eq.refl at every shape environment, \
             term, shape, derivation and valuation.",
        ),
        "r17_xval_zeta_reads_value" => (
            &["xval", "WKC.let_", "vconsD", "Eq.refl"],
            "The POSITIVE half of the let_ clause's NON-DEGENERACY, at a term whose value is a \
             VARIABLE: the interpretation of `let x : Sort 0 := bvar 0; x` IS the valuation's own \
             slot 0, at every valuation. Its paired refusal probe shows the junk-extended reading \
             is a DIFFERENT value. Both constraints on the spelling were MEASURED (R17 cycle 3, \
             where the first probe was accepted and witnessed nothing): the value cannot be a \
             sort, because xval sends every sort to the TOP candidate and junkD (Sk.kd Sk.ty) IS \
             the top candidate; and the valuation cannot be r12_betaJunkEnv, which is junk at \
             every index.",
        ),
        "r17_wkc_step_let_witness" => (
            &["wkc_step", "r17_let_witness", "beta_reduces.zeta"],
            "wkc_step run on the ZETA REDEX, through the whole letRedex_whnf_inv and out at \
             wkc_inst. The let_ arm's real exercise.",
        ),
        "r17_wkc_lift_konst_witness" => (
            &["wkc_lift0", "r17_konst_witness"],
            "Weakening at the konst arm: lifting does not move a constant and the derivation \
             survives into the extended shape environment.",
        ),
        "r17_deriv_unique_witness" => (
            &["r17_wkc_deriv_unique", "r17_wk_wkc", "r15_instDeriv", "r17_wkc_step_let_witness"],
            "NON-VACUITY of the subsingleton at two derivation TERMS built by genuinely different \
             routes: R14's wk_inst pushed through the embedding, and this rung's own wkc_step run \
             on the zeta redex. This constant proves them EQUAL.",
        ),
        "r17_irrel_witness" => (
            &["r17_xval_irrel", "r17_wk_wkc", "r15_instDeriv", "r17_wkc_step_let_witness"],
            "Irrelevance at that same pair. The paired refusal test measures that the equation is \
             NOT provable by Eq.refl, so the witness is not definitional in disguise.",
        ),
        "r17_unrestricted_konst_refuted" => (
            &["AndType.intro", "PropBox", "the_red_env_delta_nonvacuous", "r17_notArrT", "r17_shape_correct"],
            "THE PROVED OBSTRUCTION: an UNRESTRICTED konst rule loses subject reduction. One \
             kernel-checked constant pairing a REAL delta step out of a REAL reflected constant — \
             the_red_env_delta_nonvacuous, whose target is a lam, which is R9's finding that every \
             real body in the_red_env is one — with the proof that no lam can carry the shape \
             Sk.ty a const rule assigns. The inertness premise is FORCED, not chosen. What is NOT \
             refuted: a constant SHAPE ENVIRONMENT with a soundness condition tying it to \
             the_red_env's bodies; that is a rung of its own.",
        ),
        "r17_constructor_gap_closed" => (
            &["AndType.intro", "r17_konst_witness", "r17_let_witness"],
            "THE RUNG'S HEADLINE CONTRAST, in one constant: both new constructors, inhabited at \
             REAL objects — a real reflected kernel constant and R15's own unreachable let term.",
        ),
        _ => (&[], "R17 constructor gap: const and let_ on the WK/sval lineage."),
    }
}

impl Specification {
    /// Register R17: the constructor gap — `const` and `let_` with the whole
    /// R14-R16 operation stack, and the settled conversion-rule question.
    pub(super) fn add_candmodel_construct_r17(&mut self) -> Result<(), SpecError> {
        for item in r17_items() {
            match item {
                R17Item::Ind { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_inductive(&src, desc)?;
                }
                R17Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R17Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r17_tests.rs"]
mod tests;
