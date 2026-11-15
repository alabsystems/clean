// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R25 of the candidate-model construction ladder — **THE ARROW CANDIDATE**:
//! the non-dependent function type over R17's system, with both the
//! introduction and the elimination rule a Tait fundamental theorem needs at
//! it.
//!
//! ## Why this rung
//!
//! R24 landed the reducibility interface and R1's β engine on it, and named the
//! remaining gap as a term typing judgment. A judgment is not the first thing
//! to build: its `lam` and `app` rules have to have SEMANTIC counterparts
//! first, and those counterparts are about a TYPE FORMER that does not yet
//! exist on this lineage. This rung builds the former and both counterparts.
//!
//! ## A — the type former, and the shape arithmetic it depends on
//!
//! `r25_arrow A B` is `KExpr.pi A (lift_at B 0 1)` — the de Bruijn spelling of
//! a non-dependent `A -> B`. Two computations have to line up for
//! `r25_arrowWkc` to typecheck, and neither is arranged here:
//!
//! * `piShape Sk.ty t` computes to `Sk.ty`, so a `pi` of two TYPES is itself a
//!   type and `WKC.pi` concludes where it must.
//! * `domSk Sk.ty` computes to `Sk.ty`, so the codomain premise sits in
//!   `skcons Sk.ty D` and `wkc_lift0 D B Sk.ty hB Sk.ty` produces exactly it.
//!
//! Both are R12's definitions computing. This is the first place in the ladder
//! that depends on them agreeing, which is why the definition is registered
//! rather than inlined.
//!
//! ## B — the membership IS the function space, definitionally
//!
//! `r25_red_arrow_is_the_function_space` is `Eq.refl`. At a `pi` of two types,
//! `xval` denotes `mkTyD Sk.ty Sk.ty (PiSet …)`, and `mkTyD Sk.ty t C` computes
//! to `C` while `vcarD Sk.ty V` computes to `V` — so reducibility at `A -> B`
//! unfolds, with no lemma, to
//!
//! ```text
//! forall a, RedAt A a -> B' (app t a)
//! ```
//!
//! where **`B'` is the codomain read LIFTED, at the junk extension**. That is
//! the one place the non-dependence is visible: `xval`'s `pi` clause always
//! reads its codomain at a junk-extended valuation, which is exactly right for
//! a codomain that does not mention the bound variable and is why this former
//! is spelled with a lift.
//!
//! **`r20_xval_lift0` is what identifies `B'` with `B`**, and it is the only
//! work in either rule. It was built in R20 for `r20_xvenvSub_up`'s successor
//! branch; this is its second consumer and the one that pays for the lift in
//! the type former.
//!
//! ## C — the two rules
//!
//! * **`r25_red_app`** — reducible at `A -> B` applied to reducible at `A` is
//!   reducible at `B`. The `app` case of a fundamental theorem, and it is the
//!   unfolding plus one transport.
//! * **`r25_red_lam`** — a lambda whose body's contractum is reducible at `B`
//!   for every reducible argument and every `betaStar`-development of the body
//!   is reducible at `A -> B`. The `lam` case, and the one that needed an
//!   ENGINE: it is `r24_red_beta_expand` under the same transport run the other
//!   way. The family-shaped premise is R1's honest interface, not a weakening
//!   chosen here — R1 records that the single-contractum spelling needs
//!   substitution-step lemmas that do not exist spec-side.
//!
//! Both are pinned by refusals. `r25_app_no_transport_probe` drops the
//! transport and hands the application back directly; the kernel refuses,
//! because `hf a ha` inhabits the LIFTED reading and not `B`'s own.
//! `r25_lam_no_acc_probe` drops the engine's two `whnf_acc` premises; refused,
//! because the redex's normalization is not free.
//!
//! ## What this rung does NOT do
//!
//! * **There is still no term typing judgment, and this rung does not add
//!   one.** What it adds is the pair of semantic rules such a judgment's `lam`
//!   and `app` cases would discharge against. Writing the judgment itself needs
//!   a term context of TYPES with lifting under binders, and its fundamental
//!   theorem needs a substitution-composition lemma
//!   (`instantiate (psubst (up σ) b) a = psubst (scons a σ) b`) that R1 records
//!   as deferred work — its module doc says the substitution-step lemmas "do
//!   NOT exist spec-side". That lemma, not the engine, is now the next concrete
//!   obligation.
//! * **The fragment is ζ-free and NON-DEPENDENT.** `let_` is excluded because
//!   R24's contrast shows no per-set engine can reach it; dependence is
//!   excluded because `xval`'s `pi` clause reads its codomain at junk, which is
//!   R17's recorded `piShape` erasure. Both exclusions are visible in the type
//!   former rather than hidden in a proof.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 2 `add_recursive_def` and 4
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking.

use std::collections::HashSet;

use super::candmodel_construct_r25_src::{r25_items, R25Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R24's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R25 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r25_arrow" => (
            &["KExpr.pi", "lift_at"],
            "THE NON-DEPENDENT FUNCTION TYPE, spelled in de Bruijn as a pi whose codomain is \
             lifted past the binder. The lift is not decoration: xval's pi clause always reads its \
             codomain at a JUNK-extended valuation, which is exactly right for a codomain that \
             does not mention the bound variable.",
        ),
        "r25_arrowWkc" => (
            &["WKC.pi", "wkc_lift0", "piShape", "domSk"],
            "Its shape derivation, and the place the shape arithmetic has to work out. piShape \
             Sk.ty t computes to Sk.ty, so a pi of two TYPES is itself a type; domSk Sk.ty computes \
             to Sk.ty, so the codomain premise sits in skcons Sk.ty D and wkc_lift0 produces \
             exactly it. Both are R12's definitions computing, and this is the first place in the \
             ladder that depends on them agreeing.",
        ),
        "r25_red_arrow_is_the_function_space" => (
            &["r24_RedAt", "r25_arrow", "PiSet", "Eq.refl"],
            "THE MEMBERSHIP IS THE FUNCTION SPACE, DEFINITIONALLY — Eq.refl. mkTyD Sk.ty t C \
             computes to C and vcarD Sk.ty V computes to V, so reducibility at A -> B unfolds with \
             no lemma to `forall a, RedAt A a -> B' (app t a)`, where B' is the codomain read \
             LIFTED at the junk extension. Registered so nobody re-derives it from three \
             definitions computing.",
        ),
        "r25_red_app" => (
            &["r24_RedAt", "r25_arrowWkc", "r20_xval_lift0", "Eq.substType"],
            "THE ELIMINATION RULE, and the app case of a Tait fundamental theorem over this \
             lineage: reducible at A -> B applied to reducible at A is reducible at B. The \
             unfolding is definitional; the only work is identifying the lifted codomain reading \
             with B's own, which is r20_xval_lift0 — built in R20 for venvSub_up's successor branch \
             and paying here for the lift in the type former.",
        ),
        "r25_red_lam" => (
            &["r24_red_beta_expand", "r20_xval_lift0", "Eq.symm", "Eq.substType"],
            "THE INTRODUCTION RULE, and the lam case — the one that needed an ENGINE. It is \
             r24_red_beta_expand under the same r20_xval_lift0 transport run the other way. The \
             family-shaped premise (every betaStar-development of the body, every reducible \
             argument) is R1's honest interface and not a weakening chosen here: R1 records that \
             the single-contractum spelling needs substitution-step lemmas that do not exist \
             spec-side.",
        ),
        "r25_red_arrow_members_sn" => (
            &["r24_red_members_sn", "r25_arrowWkc"],
            "A term reducible at a function type NORMALIZES. R24's members_sn at the arrow type, \
             which is an ordinary ty-shaped type here — NOT one of the degenerate arrow-SHAPED \
             instances R23 measured.",
        ),
        _ => (
            &[],
            "R25 arrow candidate: the non-dependent function type and its two semantic rules.",
        ),
    }
}

impl Specification {
    /// Register R25: the arrow candidate and its two rules.
    pub(super) fn add_candmodel_construct_r25(&mut self) -> Result<(), SpecError> {
        for item in r25_items() {
            match item {
                R25Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R25Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r25_tests.rs"]
mod tests;
