// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R22 of the candidate-model construction ladder — **THE NATIVE CONVERSION
//! LEMMA**, and with it the whole R14/R16 semantic stack standing on `WKC`
//! rather than on the five-constructor system it extends.
//!
//! ## Why this rung is short
//!
//! R21 closed by naming this and by saying what shape it would be: *"a
//! `whnfStar` induction rather than a `WKC` one — a different shape of work from
//! R19-R21."* That is exactly why it is short. `r22_xval_star_sem` has TWO arms,
//! `refl` and `step`, and neither of them knows how many constructors the shape
//! system has; the seven-constructor work is all inside `r21_xval_step_sem`,
//! which this consumes once, in the `step` arm.
//!
//! ## A — conversion needs no box and no irrelevance hypothesis
//!
//! Two things about `r22_xval_conv` are worth stating, because both differ from
//! how the `sval` side got there.
//!
//! **No `PropBox`.** R16 needed the box for `val_step` and `val_step_star`
//! because their conclusions are `Eq`s, which live in Prop, while the CPS
//! continuation quantifies over `C : Type`. `val_conv`'s conclusion is a
//! MEMBERSHIP — `vcarD s v t` is a `Type` — so it is handed to
//! `r22_xval_star_sem` as its own `C` directly. The lemma is then one
//! application of the star form, one `Eq.trans` and one `Eq.substType`.
//!
//! **No irrelevance hypothesis.** R15 could only state `val_conv` conditionally
//! on one (`r15_val_conv_from_irrel`), and R16 discharged it with
//! `r16_sval_irrel`. Here the derivation `zhw` that the star form hands back at
//! the FIRST reduction sequence is reused at the SECOND, so the two
//! interpretations are related without ever comparing two derivations of one
//! judgment. The subsingleton is still used — inside `r22_xval_step_star` — but
//! conversion itself no longer needs it as a premise.
//!
//! ## B — what now stands natively, and what that is and is not
//!
//! With this rung the semantic operation stack over R17's seven-constructor
//! system is complete:
//!
//! | lemma | native since | reaches `konst`/`let_` |
//! |---|---|---|
//! | `val_lift` | R19 | yes |
//! | `val_psub` / `val_inst` / β | R20 | yes |
//! | `val_step` | R21 | yes |
//! | `val_step_star` / `val_conv` | R22 | yes |
//!
//! Every one of R18's transported theorems now has a native counterpart, and
//! each rung pins that with a drift check stating R18's TYPE and proving it with
//! the native VALUE (`r22_step_star_extends_transported`,
//! `r22_conv_extends_transported` here).
//!
//! **What this is.** The layer a reducibility argument stands on: weakening,
//! substitution, instantiation, β, one step, and conversion, all over a system
//! that has `const` and `let_`.
//!
//! **What this is not.** It is not a reducibility argument, and it is not an SN
//! result. **PARTIALLY ANSWERED 2026-09-17 by R23**, which carried R12's
//! adequacy chain across — `r23_xval_good`, `r23_isCandHI_xval`,
//! `r23_xval_members_sn`, `r23_xval_excludes_omega` — giving an UNCONDITIONAL
//! normalization statement over the seven-constructor system, non-vacuous at
//! both new constructors. That is still not the SN capstone: `WKC` is a SHAPE
//! system and `whnf_terminates_well_typed_dependent` is about `TypingCtx`, the
//! dependent TERM judgment. R23 also computed the scope of every
//! membership-shaped result in R18-R23, this rung's `r22_xval_conv` included:
//! `vcarD` at an ARROW shape discards its value, so conversion is the identity
//! there and its content lives at `ty` and `kd`. Nothing in R18-R22 advances
//! `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`,
//! and nobody should read "the semantic stack is native" as progress on either.
//! `WKC` still has SEVEN constructors against `KExpr`'s nine — no `proj`, no
//! `lit` — still has no conversion RULE (R17 measured that adding one keeps
//! shape uniqueness and loses derivation uniqueness, `r17_conv_verdict`), still
//! carries shapes rather than types in its context, and still restricts `konst`
//! to INERT constants. Those are the distances to `TypingCtx`, and none of them
//! moved.
//!
//! ## The named next item
//!
//! **The constant SHAPE ENVIRONMENT.** R17 named it — *"a constant shape
//! environment plus a soundness condition against `the_red_env`"* — and proved
//! the cheap version of it refuted (`r17_unrestricted_konst_refuted`: a
//! `Sk.ty`-valued rule at a δ-ACTIVE constant loses subject reduction outright,
//! because every real body in `the_red_env` is a `lam` and a `lam`'s shape is an
//! `Sk.arr`). It is the last thing between `WKC.konst` and `TypingCtx.const`,
//! which reads a declared type off a `tenv`. Now that the semantic stack is
//! native, that rung's cost is visible: a `Name -> Sk` environment changes the
//! `konst` clause of `xval` from the top candidate to an environment lookup, and
//! every `Eq.refl` this ladder has been collecting at the `konst` arm — three of
//! them, in R19, R20 and R21 — becomes real work, with the δ-step case
//! genuinely open rather than refuted.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 1 `add_recursive_def` and 7
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking.

use std::collections::HashSet;

use super::candmodel_construct_r22_src::{r22_items, R22Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R21's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R22 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r22_xval_star_sem" => (
            &["whnfStar.rec", "r21_xval_step_sem", "xval", "Eq.trans"],
            "R15's val_star_sem over WKC/xval. An induction on whnfStar, not on the derivation, so \
             it has exactly TWO arms and neither knows how many constructors the shape system has \
             — the seven-constructor work is all inside r21_xval_step_sem, consumed once in the \
             step arm. That is why this rung is short where R19-R21 were long.",
        ),
        "r22_xval_step_star" => (
            &["r22_xval_star_sem", "r16_unbox", "PropBox", "r17_xval_irrel"],
            "The forall-form along a whole reduction sequence. R16's val_step_star with PropBox \
             reused for the Type/Prop mismatch and r17_xval_irrel in place of r16_sval_irrel.",
        ),
        "r22_xval_conv" => (
            &["r22_xval_star_sem", "r22_xval_step_star", "Eq.substType", "vcarD"],
            "THE NATIVE CONVERSION LEMMA, at seven constructors. NO PropBox: val_conv's conclusion \
             is a MEMBERSHIP, and vcarD s v t is a Type, so it is handed to r22_xval_star_sem as \
             its own C directly. NO irrelevance hypothesis either: R15 could only state val_conv \
             conditionally on one and R16 discharged it, but here the derivation the star form \
             hands back at the FIRST sequence is reused at the SECOND, so the two interpretations \
             are related without ever comparing two derivations of one judgment.",
        ),
        "r22_step_star_extends_transported" => (
            &["r22_xval_step_star", "r17_wk_wkc"],
            "DRIFT CHECK: R18's r18_xval_step_star TYPE proved with R22's native VALUE.",
        ),
        "r22_conv_extends_transported" => (
            &["r22_xval_conv", "r17_wk_wkc"],
            "DRIFT CHECK: R18's r18_xval_conv TYPE proved with R22's native VALUE. With this and \
             the three before it, every transported theorem of R18 has a native counterpart whose \
             statement has been checked against the transported one.",
        ),
        "r22_letStar" => (
            &["whnfStar.step", "whnfStar.refl", "r17_letTerm", "beta_reduces.zeta"],
            "R17's let_ witness reduces to its zeta contractum in ONE step, hence one whnfStar \
             link. The object the two reach witnesses are stated at.",
        ),
        "r22_step_star_reaches_let" => (
            &["r22_xval_step_star", "r22_letStar", "r17_let_witness"],
            "The forall-form star law at that zeta sequence — a REAL reduction out of a REAL let_.",
        ),
        "r22_conv_reaches_let" => (
            &["r22_xval_conv", "r22_letStar", "r17_let_witness"],
            "CONVERSION across that zeta step, carrying an arbitrary membership. Stated as a \
             function of the membership rather than at a fixed inhabitant, because what is claimed \
             is the TRANSPORT and not the existence of a particular element.",
        ),
        _ => (
            &[],
            "R22 native conversion: val_step_star and val_conv by whnfStar induction.",
        ),
    }
}

impl Specification {
    /// Register R22: the native conversion lemma.
    pub(super) fn add_candmodel_construct_r22(&mut self) -> Result<(), SpecError> {
        for item in r22_items() {
            match item {
                R22Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R22Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r22_tests.rs"]
mod tests;
