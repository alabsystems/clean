// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R21 of the candidate-model construction ladder — **THE NATIVE STEP LAW**:
//! subject reduction carrying a semantic equation, by induction on `WKC`, at
//! all seven constructors.
//!
//! ## Why this rung
//!
//! R20 closed by naming this: *"the step law is still not native … what R20
//! supplies is the missing INGREDIENT — a native `val_inst`, hence a native β
//! law — not the induction over `whnf_step` itself."* This is that induction.
//!
//! **`r21_xval_step_sem`** is R15's `val_step_sem` at seven constructors: from
//! a `whnf_step` out of a `WKC`-typed term, hand back a `WKC` derivation of the
//! reduct TOGETHER WITH the equation saying its interpretation is the original's.
//! **`r21_xval_step`** is the ∀-form at any derivation of the reduct.
//!
//! ## A — what each arm cost, and what it reused
//!
//! The five old arms are R15's with `sval` → `xval`, `r14_wkCastT` →
//! `r17_wkcCastT` and `r14_sval_cast_term` → `r20_xval_cast_term`. **R20's
//! `r20_xval_cast_term` was built for exactly this and is spent in every
//! congruence case of every arm** — nine times in all. The value-level
//! congruences (`r14_sval_pi_congr`, `r14_vapply_congr`, `r13_vd_arr_funext`)
//! are reused verbatim once more, for the reason R19 established: they speak
//! about values and valuations and never about a derivation.
//!
//! The `app` arm's head-β case needed the one genuinely new piece:
//! **`r21_xval_lam_inv`**, R15's semantic lambda inversion over `WKC`/`xval`.
//! `r17_wkc_lam_inv` hands back only the body DERIVATION; the β case also needs
//! the equation saying the lambda's denotation applied to a value IS the body's
//! denotation at the extended valuation, and no subsingleton argument supplies
//! it — there is no `WKC.lam` to rebuild, the annotation's own derivation not
//! being exposed. So the inversion is computed the way R15 computes its own:
//! `r21_xvalLamT` is a nine-armed `KExpr.rec` landing in `ConstFreeUnit` at
//! eight heads and in the real obligation at a `lam` of ARROW shape, and every
//! impossible head then dies by COMPUTATION rather than by a discrimination
//! lemma.
//!
//! ## B — the two new arms
//!
//! * **`konst` is a REFUTATION, not a proof.** An inert constant admits no
//!   `whnf_step` at all (`r17_const_no_step`), so the arm discharges its own
//!   continuation type from the step itself. This is the third rung in a row
//!   where `konst` costs nothing, and the reason is always the same: R17 bought
//!   it by restricting the rule to inert constants, and `r17_unrestricted_konst_refuted`
//!   proved that restriction forced.
//! * **`let_` has FOUR cases, and three of them are nearly free.** R1's
//!   `letRedex_whnf_inv` splits a step out of a `let_` into ζ plus congruence in
//!   the annotation, the value and the body.
//!   * **ζ** is the interesting one, and it is two steps: the cast lemma, then
//!     `r20_xval_inst`. The equation then closes on the nose, because `xval`'s
//!     `let_` clause IS the extended-valuation reading — R17's
//!     `r17_xval_zeta` = `Eq.refl`, now paying off in the place it was built for.
//!   * **the ANNOTATION case is `Eq.refl` after the cast**, because `xval` never
//!     reads a `let_`'s annotation. R19 recorded that fact about weakening; here
//!     it means a whole congruence case evaporates.
//!   * the VALUE case is one `Eq.cong` in the extension value; the BODY case is
//!     the body hypothesis at the value-extended valuation, directly.
//!
//! ## C — the ∀-form, and the subsingleton once more
//!
//! `PropBox` is R16's and is reused verbatim: `val_step_sem`'s continuation is
//! quantified over `C : Type` while the conclusion is an `Eq`, which is a Prop,
//! and R16 built the box for that mismatch. What R16 needed `r16_sval_irrel`
//! for, this rung gets from `r17_xval_irrel` — the subsingleton's fourth
//! consumer outside R17.
//!
//! ## What this rung does NOT do
//!
//! * **CLOSED 2026-09-17 by R22 — `val_step_star` and `val_conv`.** R22's
//!   `r22_xval_star_sem` consumes `r21_xval_step_sem` once, in its `step` arm,
//!   and that is the whole of the seven-constructor work in it. Two things R22
//!   measured belong here: its `val_conv` needs NO `PropBox` (a membership is
//!   already a `Type`, where an `Eq` is a Prop) and NO irrelevance hypothesis
//!   (the derivation the star form returns at the FIRST sequence is reused at
//!   the SECOND), so it is strictly cheaper than the route R15/R16 took on the
//!   `sval` side. WAS: R16 derives its `val_conv` from
//!   `r15_val_conv_from_irrel` through `r15_val_star_sem`, and the `whnfStar`
//!   induction has NOT been redone here. `r18_xval_step_star` and
//!   `r18_xval_conv` therefore remain scoped to `h : WK`. That is the named next
//!   item, and it is a `whnfStar` induction rather than a `WKC` one — a
//!   different shape of work from R19-R21.
//! * **`proj` and `lit` are still untyped**, there is still no conversion rule
//!   in `WKC`, and `konst` is still restricted to INERT constants.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!   What the last four rungs have built is the SEMANTIC OPERATION STACK over
//!   R17's seven-constructor system — weakening, substitution, instantiation, β,
//!   and now one reduction step — which is the layer a reducibility argument
//!   stands on, not the argument itself.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 2 `add_recursive_def` and 4
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking.

use std::collections::HashSet;

use super::candmodel_construct_r21_src::{r21_items, R21Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R20's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R21 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r21_xvalLamT" => (
            &["KExpr.rec", "Sk.rec", "xval", "WKC", "ConstFreeUnit"],
            "THE COMPUTED SEMANTIC LAMBDA-INVERSION TYPE, at NINE heads. ConstFreeUnit at eight of \
             them and, at a lam of ARROW shape, the real obligation: a body derivation TOGETHER \
             with the equation saying the lambda's denotation applied to a value IS the body's \
             denotation at the extended valuation. R15's discipline — the impossible heads die by \
             COMPUTATION, never by a hand-written discrimination lemma.",
        ),
        "r21_xval_lam_inv" => (
            &["WKC.rec", "r21_xvalLamT", "Eq.refl"],
            "That inversion, by WKC.rec. Six arms are ConstFreeUnit.triv; the lam arm hands back \
             its OWN body premise with Eq.refl, because xval's lam clause is literally the \
             extended-valuation reading. NEEDED because r17_wkc_lam_inv gives only the DERIVATION \
             and the head-beta case also needs the equation — and no subsingleton argument \
             supplies it, there being no WKC.lam to rebuild without the annotation's derivation.",
        ),
        "r21_xval_step_sem" => (
            &[
                "WKC.rec",
                "r15_whnf_stepT_inv",
                "letRedex_whnf_inv",
                "r20_xval_cast_term",
                "r20_xval_inst",
                "r21_xval_lam_inv",
                "r17_const_no_step",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
            ],
            "THE NATIVE STEP LAW: R15's val_step_sem at SEVEN constructors. Five arms are R15's \
             with sval -> xval and the casts moved to r17_wkcCastT / r20_xval_cast_term. konst is \
             a REFUTATION (an inert constant admits no whnf_step at all). let_ has FOUR cases: \
             zeta closes through r20_xval_inst and then on the nose, because xval's let_ clause IS \
             the extended-valuation reading; the ANNOTATION case is Eq.refl after the cast, xval \
             never reading a let_'s annotation; the value case is one Eq.cong; the body case is \
             the body hypothesis at the value-extended valuation.",
        ),
        "r21_xval_step" => (
            &["r21_xval_step_sem", "r16_unbox", "PropBox", "r17_xval_irrel"],
            "The forall-form at ANY derivation of the reduct. PropBox is R16's and is reused \
             verbatim for the Type/Prop mismatch it was built for; what R16 needed r16_sval_irrel \
             for, this gets from r17_xval_irrel — the subsingleton's fourth consumer outside R17.",
        ),
        "r21_step_extends_transported" => (
            &["r21_xval_step", "r17_wk_wkc"],
            "THE DRIFT CHECK: R18's r18_xval_step TYPE proved with R21's native VALUE. ONE step, \
             because both statements read xval on both sides and only the binder differs — unlike \
             R20's, where the two valuations differed and a bridge was needed.",
        ),
        "r21_step_reaches_let" => (
            &["r21_xval_step", "r17_let_witness", "r17_wkc_step_let_witness"],
            "THE CLAIM AT AN OBJECT: the native step law at R17's let_ witness, whose step is a \
             REAL zeta reduction out of a REAL let_. r18_xval_step has no instance of this at all.",
        ),
        _ => (
            &[],
            "R21 native step law: subject reduction with a semantic equation, by induction on WKC.",
        ),
    }
}

impl Specification {
    /// Register R21: the native step law.
    pub(super) fn add_candmodel_construct_r21(&mut self) -> Result<(), SpecError> {
        for item in r21_items() {
            match item {
                R21Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R21Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r21_tests.rs"]
mod tests;
