// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R28 of the candidate-model construction ladder — **THE TYPE VOCABULARY**:
//! `InertTy`, the `ty`-shaped types a term judgment on this lineage can be
//! stated over, with the three facts about them a Tait `lam` case consumes.
//!
//! ## Why this rung
//!
//! `docs/issues/2026-09-17-fundamental-theorem-route-on-the-wkc-lineage.md`
//! ends: *"What remains is the JUDGMENT, not a lemma — a term context of TYPES
//! with lifting under binders, and a reducible-substitution predicate. Neither
//! is hard; neither is written."* R27 then supplied the two facts about
//! `r24_RedAt` itself that such an induction needs. This rung supplies the
//! third missing piece, and it is the one that sentence did not anticipate:
//! **a class of types the substitution and the lift both FIX.**
//!
//! The full design, with the measurements behind every choice, is
//! `designs/2026-09-17-r28-term-judgment-on-the-wkc-lineage.md`.
//!
//! ## A — why a type class is needed at all, and how it was found
//!
//! A Tait `lam` case closes with `r26_red_lam_one`, which demands
//! `whnf_acc ann` and `whnf_acc b` at the SUBSTITUTED terms. That looked like
//! this rung's real cost. **It is not, and the answer was read out of R6's own
//! proof term** (`val_synty_fundamental`), whose two inline comments name both
//! mechanisms: the annotation's SN comes "through SimpleTy" — rewrite
//! `psubst s A` back to `A` by `simpleTy_psubst`, because simple types are
//! CLOSED, then read SN off `simpleTy_whnfAcc` — and the body's comes from the
//! induction hypothesis at `idsubst` plus `psubst_id`.
//!
//! **So the prerequisite is a class of types substitution fixes, and R6's does
//! not port.** `SimpleTy`'s base case is a SORT, and `WKC.sort` concludes at
//! `Sk.kd Sk.ty`, not `Sk.ty` — a sort is not a `ty`-shaped type here, and
//! `r24_RedAt`, indexed by `WKC D A Sk.ty`, cannot be stated at one.
//! `WKC.konst`'s inert reflected constants are the `ty`-shaped base instead.
//!
//! ## B — the lift, which is the whole difference from R6
//!
//! `r25_arrow A B` is `KExpr.pi A (lift_at B Nat.zero (Nat.succ Nat.zero))`:
//! non-dependence faked inside a dependent `pi`. `SimpleTy.arrow` concludes at
//! a bare `KExpr.pi A B` and never meets a lift. Every lemma here pays for it
//! exactly once, and `r28_inertTy_lift` is the payment.
//!
//! **The generalisation in that lemma is the trick, and it is worth stating
//! because the obvious route is wrong.** The instance actually wanted is
//! `lift_at T Nat.zero (Nat.succ Nat.zero) = T`, and that instance does NOT
//! admit an induction: `lift_at`'s `pi` clause recurses on the codomain at
//! `Nat.succ cutoff`, so the arrow arm needs the lemma at a depth the fixed
//! statement cannot supply. Quantifying over `d` and `k` repairs it in two
//! lines. The route that looked necessary — prove `InertTy T -> is_closed_at T
//! Nat.zero` and feed `lift_invariant_closed` — is a whole bridge, and it is
//! not needed. `r28_lift_fixed_depth_probe` pins the refusal.
//!
//! ## C — what each constant is for
//!
//! | constant | consumed by |
//! |---|---|
//! | `r28_inertTy_wkc` | every statement that needs `WKC D T Sk.ty` from a type, at any `D` |
//! | `r28_inertTy_lift` | the other two, and `r25_arrow`'s codomain everywhere |
//! | `r28_inertTy_psubst` | removes every `psubst` reshaping from a fundamental theorem's TYPE side |
//! | `r28_inertTy_whnfAcc` | `r26_red_lam_one`'s `whnf_acc ann` premise |
//! | `r28_inertTy_not_total` | nothing — it is the NON-DEGENERACY of the class |
//!
//! The `konst` arm of `r28_inertTy_whnfAcc` is free for a sharper reason than
//! R6's: `r17_const_no_step` is a CPS inverter — given any `whnf_step` out of
//! an inert constant it returns ANY type — so accessibility is discharged by a
//! function with no cases, not by a landed SN theorem.
//!
//! ## What this rung does NOT do
//!
//! * **It is not the judgment.** `TmC`, `r28_ctxOK`, `r28_RedSub` and the
//!   fundamental theorem are the next increment; the design doc has all four
//!   statements. This rung is their vocabulary, and it is separated because a
//!   new inductive plus a generalised induction is enough for one elaboration
//!   cycle on this box.
//! * **`InertTy` is CLOSED types only** — no `WKC.var`, no `WKC.let_`, no
//!   `WKC.app`. That is not a simplification for convenience: it is what makes
//!   `psubst` and `lift_at` inert, which is what R6's `lam` arm needs. A wider
//!   class buys a wider judgment and a harder `lam` case, in that order.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## Census
//!
//! ONE new inductive (`InertTy`, two constructors) and ZERO new axioms: one
//! plain definition plus five value-bearing theorems through `add_definition`
//! with kernel `add_decl` checking. Axiom closure as R27's.

use std::collections::HashSet;

use super::candmodel_construct_r28_src::{r28_items, R28Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R27's theorem helper, verbatim: one `add_definition` per theorem so the
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

/// `(dependencies, description)` for every R28 constant. One row each, so the
/// census/coverage tooling SEES each name with its own meaning.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "InertTy" => (
            &["r25_arrow", "the_red_env"],
            "THE TYPE CLASS, and R6's SimpleTy does not port. Two constructors: an inert \
             reflected constant, carrying WKC.konst's two inertness equations verbatim, and \
             r25_arrow. The base case is a CONSTANT rather than a sort because WKC.sort \
             concludes at Sk.kd Sk.ty and not at Sk.ty, so a sort is not a ty-shaped type on \
             this lineage and r24_RedAt -- which is indexed by WKC D A Sk.ty -- cannot be stated \
             at one. Closed types only, and deliberately: closedness is exactly what makes \
             psubst and lift_at inert, which is what a Tait lam case needs. Census: one new \
             inductive, zero axioms.",
        ),
        "r28_inertTy_wkc" => (
            &["InertTy.rec", "WKC.konst", "r25_arrowWkc"],
            "Every inert type is ty-shaped, at EVERY shape environment. D is bound outside the \
             induction because no clause changes it -- InertTy mentions no environment at all, \
             which is the point of restricting to closed types. The konst arm hands WKC.konst \
             back the two equations InertTy.konst was carrying; the arrow arm is r25_arrowWkc, \
             whose own typing rests on piShape Sk.ty t = Sk.ty and domSk Sk.ty = Sk.ty.",
        ),
        "r28_inertTy_lift" => (
            &["InertTy.rec", "lift_at", "Eq.substType"],
            "LIFTING FIXES AN INERT TYPE, at every cutoff and amount -- and the GENERALISATION \
             is the content. The instance actually wanted is lift_at T 0 1 = T, and that \
             instance admits no induction: lift_at's pi clause recurses on the codomain at \
             Nat.succ cutoff, so the arrow arm needs the lemma at a depth the fixed statement \
             cannot supply. Quantifying over d and k repairs it in two lines, and the route that \
             looked necessary -- InertTy T -> is_closed_at T 0, then lift_invariant_closed -- is \
             a whole bridge that is not needed. The arrow arm uses its IH three times: at (0,1) \
             to see through r25_arrow's own lift, at (succ d, k) for the codomain, at (d,k) for \
             the domain. R6 never met any of this, SimpleTy.arrow concluding at a bare \
             KExpr.pi A B with no lift.",
        ),
        "r28_inertTy_psubst" => (
            &["InertTy.rec", "r28_inertTy_lift", "psubst", "up"],
            "SUBSTITUTION FIXES AN INERT TYPE, for every substitution -- simpleTy_psubst's \
             analogue, and its own description gives the reason in one line: simple types are \
             closed, so substitution is inert. The arrow arm has to see through r25_arrow's lift \
             first, which is what r28_inertTy_lift is for, used at (0,1) and rewritten back. \
             THIS IS WHAT REMOVES EVERY psubst RESHAPING FROM THE TYPE SIDE of a fundamental \
             theorem, exactly as R6's synTy_fundamental needs no psubst_instantiate.",
        ),
        "r28_inertTy_whnfAcc" => (
            &[
                "InertTy.rec",
                "whnf_acc.intro",
                "r17_const_no_step",
                "whnfAcc_pi",
                "r28_inertTy_lift",
            ],
            "EVERY INERT TYPE IS STRONGLY NORMALIZING -- the premise r26_red_lam_one takes as \
             whnf_acc ann, and R6 gets its analogue the same way through whnfAcc_sort and \
             whnfAcc_pi. Here the base case is a CONSTANT rather than a sort, and it is free for \
             a sharper reason than R6's: r17_const_no_step is a CPS inverter, so given any \
             whnf_step out of an inert constant it returns any type at all, and the \
             accessibility arm is discharged by a function with NO CASES rather than by a landed \
             SN theorem. The arrow arm is whnfAcc_pi with r28_inertTy_lift collapsing \
             r25_arrow's codomain lift.",
        ),
        "r28_notBvar" => (
            &["KExpr.rec", "ConstFreeUnit"],
            "The head discriminator the non-degeneracy proof needs: KExpr.rec into Type, bvar to \
             Empty and every other head to ConstFreeUnit. Its nine-minor shape is \
             kapp_head_bvar_absurd's (hnf3_residual.rs), re-spelled per this rung's no-imports \
             convention and simplified -- that one descends the application spine, which this \
             has no use for.",
        ),
        "r28_inertTy_not_total" => (
            &["InertTy.rec", "r28_notBvar", "Eq.substType"],
            "NON-DEGENERACY, and it is a PROOF rather than a refused probe -- the difference \
             being that a refusal says the kernel would not accept one derivation while this \
             says no derivation exists. Without it InertTy could be true of everything and all \
             four lemmas above would be kernel-checked statements about everything. R6 pins \
             exactly this with simpleTy_not_total. bvar is the sharpest witness available: it is \
             precisely the shape restricting to CLOSED types excludes, and closedness is what \
             makes psubst and lift_at inert, which is the entire reason the class exists. \
             Standard equality-generalised inversion, both arms transporting r28_notBvar.",
        ),
        _ => (&[], "R28 type vocabulary: InertTy and its facts."),
    }
}

impl Specification {
    /// Register R28: the `InertTy` class and the three facts about it.
    pub(super) fn add_candmodel_construct_r28(&mut self) -> Result<(), SpecError> {
        for item in r28_items() {
            match item {
                R28Item::Ind { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_inductive(&src, desc)?;
                }
                R28Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R28Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r28_tests.rs"]
mod tests;
