// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R20 of the candidate-model construction ladder — **THE NATIVE SUBSTITUTION
//! LEMMA**, the definition two rungs declined to invent, and the native β law
//! that falls out of it.
//!
//! ## Why this rung, and why it could not be the last one
//!
//! R18 transported R14's `val_psub` onto `xval` and recorded a caveat in its own
//! doc: the right-hand side still read `venvSubD`, which is `WK`-indexed,
//! because *"a `WKC`-indexed valuation construction is a DEFINITION, not a
//! corollary of this rung, and inventing it here would put an unproved
//! `xval`-side object inside a theorem that is otherwise pure transport."* R19
//! took `val_lift` native and repeated the same point about `psub`, calling it
//! *"strictly harder"* for exactly this reason.
//!
//! Both were right, and the fix is not clever: **make the definition, in its own
//! rung, the way `venvSubD` was made in R14.** `r20_xvenvSubD` is `venvSubD`
//! with `WK`/`sval` replaced by `WKC`/`xval`, and everything else here follows.
//!
//! ## A — the definition, and the one-line bridge
//!
//! **`r20_xvenvSubD_agrees`** proves the new construction IS `venvSubD` on the
//! embedded fragment, and it is one line: pointwise the claim is exactly
//! `r18_xval_sval`, and `r13_venvD_funext` turns pointwise agreement into an
//! equality of valuations.
//!
//! That bridge is load-bearing rather than decorative. The native substitution
//! lemma and R18's transported one read DIFFERENT valuation constructions on
//! their right-hand sides, so without it the two statements cannot even be
//! compared — they would drift silently past each other. With it,
//! `r20_psub_extends_transported` states R18's type and proves it from R20's
//! theorem in two steps, the second being exactly that bridge.
//!
//! **The bridge is strictly narrower than the definition, and that is pinned.**
//! `r20_agrees_at_wkc_probe` claims the agreement at an ARBITRARY `WKC`
//! substitution hypothesis and the kernel refuses it: `venvSubD` takes a
//! `WK`-typed hypothesis and at a `konst`- or `let_`-headed substitution there
//! is none to hand. The new construction is wider than the old one; the bridge
//! between them is not, and must not look as if it were.
//!
//! ## B — the substitution lemma
//!
//! **`r20_xval_psub`** is R14's `val_psub` at seven constructors. Its five old
//! arms are R14's with `sval`/`wk_psub`/`venvSubD` replaced, reusing R13's and
//! R14's value-level helpers verbatim, exactly as R19 found.
//!
//! The arms worth naming:
//!
//! * **`var` is `Eq.refl`**, and R14 already recorded why: stating the operation
//!   with a substitution HYPOTHESIS rather than a cutoff makes the derivation it
//!   produces at a variable BE the hypothesis, so the interpretation is the
//!   induced valuation on the nose. `r20_xvenvSubD` is defined to make that
//!   true, which is the point of defining it at all.
//! * **`konst` is `Eq.refl`**, for R19's reason: `psubst` leaves a constant alone
//!   and `xval`'s `konst` clause never reads the valuation.
//! * **`let_` costs one congruence more than `lam`**, in the extension value,
//!   exactly as in R19 — the clause reads the valuation extended by the VALUE's
//!   interpretation, so the value's own induction hypothesis has to be spent
//!   under `vconsD`.
//!
//! **R19 is consumed in exactly one place**: `r20_xvenvSub_up`'s successor
//! branch is `r20_xval_lift0`, which is R19's native weakening at cutoff zero.
//! Nothing else in this rung needs weakening. That is the whole dependency of
//! substitution on weakening, made visible.
//!
//! ## C — instantiation, and the native β law
//!
//! **`r20_xval_inst`** is R14's `val_inst` over `wkc_inst`: the term transport
//! off `instantiate_eq_psubst` (`r20_xval_cast_term`), the substitution lemma,
//! then `r20_xvenvSub_scons` to read the induced valuation as the extension by
//! the argument's own interpretation.
//!
//! **`r20_xval_beta`** is the payoff and the reason substitution was worth
//! proving natively rather than transporting: the interpretation of a β redex's
//! contractum equals the interpretation of the redex, at any `WKC` derivation.
//! `wkc_inst` is precisely what R17's `wkc_step` calls at its head-β arm, so
//! this is the semantic half of subject reduction's hardest case, available now
//! at all seven constructors. `r20_beta_arg_shape_probe` is its control: the
//! same statement with the argument typed at `d` instead of `domSk d` is
//! refused, so the law is reading `WKC.app`'s real shape discipline and not
//! succeeding because `domSk` collapses.
//!
//! ## What this rung does NOT do
//!
//! * **The step law is still not native.** `r18_xval_step`,
//!   `r18_xval_step_star` and `r18_xval_conv` remain transported and scoped to
//!   `h : WK`. What R20 supplies is the missing INGREDIENT — a native
//!   `val_inst`, hence a native β law — not the induction over `whnf_step`
//!   itself. That induction is R17's `wkc_step` carrying a semantic equation,
//!   and it is the named next item.
//! * **`proj` and `lit` are still untyped**, there is still no conversion rule,
//!   and `konst` is still restricted to INERT constants.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## The named next item
//!
//! **CLOSED 2026-09-17 by R21.** `r21_xval_step_sem` is the induction this
//! section sized, and it landed on the first elaboration cycle. Two things it
//! measured belong here. `r20_xval_cast_term` — built in this rung for
//! `val_inst` — is spent NINE times there, once in every congruence case of
//! every arm, so the term-cast lemma was the right thing to build. And the
//! shape-cast gap this section named turned out not to bite: `wkc_step` uses
//! `r17_wkcCastS` inside `wkc_lift_var`, which the step law never re-derives,
//! so no `xval`-side shape-cast lemma was needed after all. The one piece that
//! WAS needed and is not named below is `r21_xval_lam_inv`, the SEMANTIC
//! lambda inversion: `r17_wkc_lam_inv` hands back only the body derivation, and
//! the head-β case also needs the equation. WAS: **`val_step` by induction on
//! `WKC`.** Its shape is already fixed by two
//! things in the tree: R15's `r15_val_step_sem` gives the CPS statement (from a
//! step, produce a derivation of the reduct AND the semantic equation), and
//! R17's `wkc_step` gives the seven-arm inversion skeleton — five arms reusing
//! `r15_whnf_stepT_inv` verbatim, `konst` refuted outright by
//! `r17_const_no_step`, `let_` handled by R1's `letRedex_whnf_inv`. The
//! semantic content is now in hand: the head-β arm wants `r20_xval_beta` and
//! the ζ arm wants `r17_xval_zeta`, which is `Eq.refl`. What is NOT in hand is
//! the interaction between `r17_wkcCastT` transports and the semantic equation
//! in the congruence arms — `r20_xval_cast_term` covers the term transport, but
//! `wkc_step` also uses `r17_wkcCastS`, and no `xval`-side shape-cast lemma
//! exists yet.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 2 `add_recursive_def` and 11
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking. Axiom closure as R18/R19 — `Quot.sound` and the `Quot` type
//! formers through R13's `spec_funext`, every one already inside
//! `spec_axiom_closure::EXPLICIT_FOUNDATIONAL_BASE`.

use std::collections::HashSet;

use super::candmodel_construct_r20_src::{r20_items, R20Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R19's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R20 constant, one row each so the
/// census/coverage tooling sees each name with its own meaning.
#[allow(clippy::too_many_lines)]
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r20_xvenvSubD" => (
            &["xval", "WKC"],
            "THE DEFINITION R18 AND R19 BOTH DECLINED TO INVENT: the induced valuation of a \
             WKC-typed substitution. venvSubD (R14) is the same construction over WK and sval, \
             and it is what forced r18_xval_psub's right-hand side to stay WK-indexed. Made here \
             deliberately and in its own rung, exactly as venvSubD was made in R14.",
        ),
        "r20_idsubst_typed" => (
            &["WKC.var", "idsubst"],
            "The identity substitution is WKC-typed at every index — idsubst i is bvar i, so every \
             index is WKC.var. The supply the two reach witnesses need.",
        ),
        "r20_xvenvSubD_agrees" => (
            &["r20_xvenvSubD", "venvSubD", "r18_xval_sval", "r13_venvD_funext"],
            "THE BRIDGE, IN ONE LINE. On the embedded fragment the new valuation construction IS \
             venvSubD: pointwise the claim is exactly R18's transfer, and r13_venvD_funext makes \
             it an equality of valuations. Load-bearing, because the native and transported \
             substitution lemmas read DIFFERENT valuations and without this cannot be compared at \
             all. STRICTLY NARROWER than the definition: r20_agrees_at_wkc_probe claims it at an \
             arbitrary WKC hypothesis and the kernel refuses.",
        ),
        "r20_xval_lift0" => (
            &["r19_xval_lift", "wkc_lift0", "vconsD"],
            "R19's native weakening at the context HEAD. Definitional on both sides at cutoff \
             zero. THE ONLY PLACE this rung consumes R19 — r20_xvenvSub_up's successor branch — \
             which is the whole dependency of substitution on weakening, made visible.",
        ),
        "r20_xval_cast_term" => (
            &["r17_wkcCastT", "xval", "Eq.rec"],
            "The interpretation does not see a TERM transport. R14's r14_sval_cast_term with \
             r17_wkcCastT in place of r14_wkCastT: a based Eq.rec whose base case is Eq.refl, \
             which is why both casts were defined over a BARE Eq.rec — R14 measured that a \
             transport spelled with Eq.substType does not delta-unfold and its reflexivity base \
             never reduces.",
        ),
        "r20_xvenvSub_up" => (
            &["r20_xvenvSubD", "wkc_up", "r20_xval_lift0", "r13_venvD_funext"],
            "Substitution commutes with valuation extension, over the new construction. Zero \
             branch Eq.refl, successor branch r20_xval_lift0.",
        ),
        "r20_xvenvSub_scons" => (
            &["r20_xvenvSubD", "r17_scons_typed", "r13_venvD_funext"],
            "The single-term substitution's induced valuation is the extension by that term's own \
             interpretation.",
        ),
        "r20_xval_psub" => (
            &[
                "WKC.rec",
                "xval",
                "wkc_psub",
                "r20_xvenvSubD",
                "r20_xvenvSub_up",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
            ],
            "R14's val_psub AT SEVEN CONSTRUCTORS — the native substitution lemma. The var arm is \
             Eq.refl, and R14 recorded why: stating the operation with a substitution HYPOTHESIS \
             rather than a cutoff makes the derivation it produces at a variable BE the \
             hypothesis, so the interpretation is the induced valuation on the nose — which is \
             what r20_xvenvSubD is defined to make true. konst is Eq.refl (psubst leaves a \
             constant alone, xval's konst clause never reads the valuation); let_ costs one \
             congruence more than lam, in the extension value.",
        ),
        "r20_xval_inst" => (
            &[
                "r20_xval_psub",
                "r20_xval_cast_term",
                "r20_xvenvSub_scons",
                "wkc_inst",
                "instantiate_eq_psubst",
            ],
            "NATIVE INSTANTIATION. R14's val_inst over wkc_inst: the term transport off \
             instantiate_eq_psubst, the native substitution lemma, then r20_xvenvSub_scons to read \
             the induced valuation as the extension by the argument's own interpretation.",
        ),
        "r20_xval_beta" => (
            &["r20_xval_inst", "WKC.app", "WKC.lam"],
            "THE NATIVE SEMANTIC BETA LAW, and the reason substitution was worth proving natively \
             rather than transporting: the interpretation of a beta redex's contractum equals the \
             interpretation of the redex, at any WKC derivation. wkc_inst is precisely what R17's \
             wkc_step calls at its head-beta arm, so this is the semantic half of subject \
             reduction's hardest case, available at all seven constructors. Controlled by \
             r20_beta_arg_shape_probe, which types the argument at d instead of domSk d and is \
             REFUSED.",
        ),
        "r20_psub_extends_transported" => (
            &["r20_xval_psub", "r20_xvenvSubD_agrees", "r17_wk_wkc"],
            "THE DRIFT CHECK. R18's r18_xval_psub TYPE proved from R20's native theorem. TWO steps \
             rather than R19's one, and the extra step is exactly the caveat R18 recorded: the two \
             statements read DIFFERENT valuation constructions, so the native lemma has to be \
             pushed across r20_xvenvSubD_agrees before it can be compared with the transported one.",
        ),
        "r20_psub_reaches_konst" => (
            &["r20_xval_psub", "r17_konst_witness", "r20_idsubst_typed"],
            "THE CLAIM AT AN OBJECT: the native substitution lemma at R17's REAL inert reflected \
             constant, which no embedding reaches.",
        ),
        "r20_psub_reaches_let" => (
            &["r20_xval_psub", "r17_let_witness", "r20_idsubst_typed"],
            "The same at R17's let_ witness.",
        ),
        _ => (
            &[],
            "R20 native substitution: val_psub, val_inst and the beta law by induction on WKC.",
        ),
    }
}

impl Specification {
    /// Register R20: the native substitution lemma and the native β law.
    pub(super) fn add_candmodel_construct_r20(&mut self) -> Result<(), SpecError> {
        for item in r20_items() {
            match item {
                R20Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R20Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r20_tests.rs"]
mod tests;
