// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R29 of the candidate-model construction ladder — **THE TERM JUDGMENT AND ITS
//! FUNDAMENTAL THEOREM**, on the lineage that has the conversion-invariant
//! metatheory.
//!
//! ## What this closes
//!
//! R12 left the `SynTy`/`candInterp` lineage because R11 PROVED `candInterp` is
//! not conversion-invariant. The `WK`/`WKC`/`xval` lineage that replaced it grew
//! the whole metatheory and had **no term typing judgment at all** — so for
//! seventeen rungs the two halves of a strong-normalization argument sat in
//! different lineages:
//!
//! | | term judgment + Tait tower | conversion-invariant metatheory |
//! |---|---|---|
//! | R6-R11 (`SynTy` / `candInterp`) | YES | NO (R11's refutation) |
//! | R12-R28 (`WKC` / `xval`) | **NO** | YES |
//!
//! `TmC` and `r29_fundamental` fill that cell. `r29_sn` is the capstone:
//! `TmC G e T` implies `whnf_acc e`.
//!
//! ## The fragment, stated before the result
//!
//! **ζ-free and NON-DEPENDENT**, and neither is a convenience:
//!
//! * no `let_` rule, because R1 PROVED no per-set engine reaches a `let_`
//!   redex — `Neutral (let_ …)` is `Empty` where `Neutral (app …)` is
//!   inhabited, and that single difference is the whole reason β is available
//!   per-set and ζ is not;
//! * no `sort` rule, because `WKC.sort` concludes at `Sk.kd Sk.ty` and not
//!   `Sk.ty`, so a sort is not a `ty`-shaped type here and `r24_RedAt` — which
//!   is indexed by `WKC D A Sk.ty` — cannot be stated at one. R6's
//!   `SimpleTy.base` IS a sort; R28's `InertTy.konst` is an inert reflected
//!   constant instead, and that substitution is forced;
//! * `r25_arrow A B` is `KExpr.pi A (lift_at B 0 1)` — non-dependence faked
//!   inside a dependent `pi`, which is what every lift in R28 is paying for.
//!
//! ## The `lam` arm, which is the rung
//!
//! `var` is the substitution hypothesis and `app` is `r25_red_app`; both are a
//! line. `lam` is ten steps, and the one that looked open for most of a day was
//! `whnf_acc (psubst (up s) b)` — SN of the SUBSTITUTED body, which
//! `r26_red_lam_one` demands and which no induction hypothesis of a textbook
//! rule reaches directly.
//!
//! **It is read off the arm's own family instance at `bvar 0`.** The family
//! premise is discharged at an arbitrary reducible `a2` by
//! `r26_lam_premise_is_the_induction_hypothesis` plus `r29_redsub_extend`;
//! instantiating it at `a2 := KExpr.bvar Nat.zero` — reducible at ANY type by
//! `r27_red_var` — gives membership of `instantiate (psubst (up s) b) (bvar 0)`,
//! `isCandHF_cr1` turns that into `whnf_acc` of it, and
//! `whnfAcc_of_instantiate_bvar0` strips the instantiation. So `r27_red_var` is
//! load-bearing twice in this rung, and neither use is visible from R27's own
//! statement.
//!
//! **R7 is the precedent, and it is exact.** `synTyT_fundamental`'s own
//! registration says its `lam` arm builds all three `candInterp_lam` premises
//! "from the ORDINARY single-body IH", and `whnfAcc_of_instantiate_bvar0` is in
//! its dependency list. R7 exists to get rid of R6's development family; this
//! rung makes the same trade one lineage over, and does not need the family
//! either.
//!
//! ## What this rung does NOT do
//!
//! * **It is not `whnf_terminates_well_typed_dependent`**, and it does not
//!   discharge `M : CandModel tenv`. The ladder still has no SN capstone in
//!   that sense.
//! * **It carries three premises and they are honest**: `GoodEnvD D r`,
//!   `RecEnvClosed (red_rec the_red_env)` — which the spec threads as a premise
//!   in 39 places rather than discharging, and which only the `lam` path needs —
//!   and a well-formed context. `r29_probe_no_redsub` pins the fourth
//!   (reducible substitution) as load-bearing rather than decorative.
//! * **`InertTy` types are CLOSED**, so this says nothing about a term whose
//!   type mentions a bound variable. Widening the type class widens the
//!   judgment and hardens the `lam` case, in that order.
//!
//! ## Census
//!
//! ONE new inductive (`TmC`, three constructors) and ZERO new axioms: five
//! plain definitions plus two value-bearing theorems through `add_definition`
//! with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r29_src::{r29_items, R29Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R28's theorem helper, verbatim.
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

fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r29_tcons" => (
            &[],
            "skcons at KExpr: the term context is a TOTAL function Nat -> KExpr, matching \
             VEnvD/GoodEnvD/wkc_up. Every context-like object from R12 onward on this lineage is \
             Nat -> X with a pointwise forall hypothesis, and ListType appears only as ListType \
             Level in WKC.konst. The cost is stated rather than hidden: a total context cannot \
             say the context ENDS, so nothing here says CLOSED TERM -- R6's synTy_sn_closed has \
             no analogue without a separate finiteness notion, and it is not needed.",
        ),
        "r29_ctxOK" => (
            &["InertTy"],
            "A context is well-formed when every slot is an inert type. InertTy and not WKC D _ \
             Sk.ty: r28_inertTy_wkc produces the latter at ANY shape environment, so the judgment \
             needs no shape environment -- which is why TmC is indexed by Nat -> KExpr alone and \
             D appears only in the fundamental theorem, bound outside the induction.",
        ),
        "r29_ctxOK_cons" => (
            &["r29_tcons", "InertTy"],
            "Extending a well-formed context with an inert type keeps it well-formed. Pointwise \
             Nat.rec, the vconsD shape.",
        ),
        "TmC" => (
            &["r25_arrow", "InertTy", "r29_tcons"],
            "THE TERM TYPING JUDGMENT the ladder has been missing since R12 left the SynTy \
             lineage. Three rules over the fragment the semantic rules actually cover: ZETA-FREE, \
             because R1 PROVED no per-set engine reaches a let_ redex (Neutral (let_ ..) is Empty \
             where Neutral (app ..) is inhabited), and NON-DEPENDENT, r25_arrow being \
             KExpr.pi A (lift_at B 0 1). No sort rule: WKC.sort concludes at Sk.kd Sk.ty, so a \
             sort is not a ty-shaped type here and r24_RedAt cannot be stated at one -- R6's \
             SimpleTy.base IS a sort and that substitution is forced. Type derivations are \
             InertTy fields rather than WKC ones, because carrying WKC would fix a shape \
             environment the judgment has no other use for.",
        ),
        "r29_RedSub" => (
            &["r24_RedAt", "r28_inertTy_wkc"],
            "R6's SubstOK, pointwise instead of through a lookup equation: a substitution is \
             reducible when every slot is reducible at its context type.",
        ),
        "r29_redsub_id" => (
            &["r27_red_var", "r29_RedSub"],
            "The identity substitution is reducible at every well-formed context -- r27_red_var \
             at every index. This is the SECOND thing R27 bought, not visible from R27's own \
             statement, and it is what lets the capstone drop the substitution.",
        ),
        "r29_redsub_extend" => (
            &["r29_ctxOK_cons", "scons", "r24_RedAt"],
            "scons of a reducible term onto a reducible substitution. Pointwise Nat.rec: the zero \
             arm is the new witness, the successor arm the old one. This is what feeds the lam \
             arm's family premise.",
        ),
        "r29_fundamental" => (
            &[
                "TmC.rec",
                "r27_red_irrel",
                "r25_red_app",
                "r26_red_lam_one",
                "r26_lam_premise_is_the_induction_hypothesis",
                "r29_redsub_extend",
                "r27_red_var",
                "whnfAcc_of_instantiate_bvar0",
                "isCandHF_cr1",
                "r24_red_isCandHF",
                "r28_inertTy_psubst",
                "r28_inertTy_whnfAcc",
            ],
            "THE FUNDAMENTAL THEOREM on the WKC/xval lineage -- the cell that was empty for \
             seventeen rungs. var is the substitution hypothesis at i, reconciled with the \
             motive's own derivation by r27_red_irrel (which is why R27 exists: every arm \
             rebuilds its type's derivation from what the induction hands back, and those are \
             never the derivation the goal names). app is r25_red_app, needing neither GoodEnvD \
             nor RecEnvClosed. \
             \
             lam is the rung, and the premise that looked open is whnf_acc of the SUBSTITUTED \
             body: r26_red_lam_one demands it and no textbook induction hypothesis reaches it \
             directly. It is READ OFF THE ARM'S OWN FAMILY INSTANCE at bvar 0 -- discharge the \
             family at a2 := KExpr.bvar Nat.zero, reducible at any type by r27_red_var, take \
             isCandHF_cr1, and strip the instantiation with whnfAcc_of_instantiate_bvar0. R7's \
             synTyT_fundamental is the exact precedent: its own registration says the lam arm \
             builds all three candInterp_lam premises from the ORDINARY single-body IH, and that \
             same lemma is in its dependency list. So R6's development family is not needed here \
             either.",
        ),
        "r29_sn" => (
            &[
                "r29_fundamental",
                "r29_redsub_id",
                "isCandHF_cr1",
                "psubst_id",
            ],
            "THE CAPSTONE: TmC G e T implies whnf_acc e, unconditionally in the term. The \
             fundamental theorem at idsubst (reducible by r29_redsub_id), isCandHF_cr1 to read SN \
             out of membership, psubst_id to drop the identity substitution -- R6's synTy_sn is \
             the same three steps. It still carries GoodEnvD D r, RecEnvClosed (red_rec \
             the_red_env) and a well-formed context; the first two because the lam path needs \
             them, the third because TmC's var rule reads the context.",
        ),
        _ => (&[], "R29 term judgment and fundamental theorem."),
    }
}

impl Specification {
    /// Register R29: the term judgment, its fundamental theorem, and the SN
    /// capstone.
    pub(super) fn add_candmodel_construct_r29(&mut self) -> Result<(), SpecError> {
        for item in r29_items() {
            match item {
                R29Item::Ind { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_inductive(&src, desc)?;
                }
                R29Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R29Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r29_tests.rs"]
mod tests;
