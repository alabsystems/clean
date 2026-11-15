// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R23 of the candidate-model construction ladder — **ADEQUACY AND
//! NORMALIZATION at seven constructors**, and the computed fact that says
//! exactly how much the membership-shaped results of R18-R22 claim.
//!
//! ## Why this rung
//!
//! R18-R22 built the semantic OPERATION stack over R17's seven-constructor
//! system. None of those rungs says the interpretation lands anywhere in
//! particular. R12 did say that, for the five-constructor system:
//! `sval_good`, `isCandHI_sval`, `sval_members_sn`, `sval_excludes_omega`.
//! This rung carries all four across, and the two new arms cost almost nothing.
//!
//! * **`konst` is `goodSet_whnfAcc`** — the top candidate is good, and that is
//!   the whole arm. Fourth rung running where R17's inertness restriction pays.
//! * **`let_` is the body's hypothesis at the valuation extended by the VALUE's
//!   interpretation**, with `goodEnvD_vconsD` supplying the extension's
//!   goodness from the value's own hypothesis. One line, and it is the same
//!   shape as `lam`'s.
//!
//! ## A — what `r23_xval_members_sn` says, and what it does not
//!
//! **It says:** every member of the candidate a `WKC`-typed term denotes, at a
//! GOOD valuation, is `whnf_acc` — accessible under `whnf_step`, i.e. with no
//! infinite reduction sequence. It is UNCONDITIONAL: there is no `CandModel`
//! hypothesis anywhere in its closure, and its computed axiom closure is empty.
//!
//! **It is not vacuous**, and that is two separate facts, both registered.
//! `r23_sn_fires_at_konst` feeds R17's `r17_konst_mem_witness` — a real
//! inhabitant of a real constant's candidate — through the theorem and gets
//! `whnf_acc` of that constant, so the candidate is INHABITED and the theorem
//! FIRES. `r23_omega_excluded_at_konst` and `r23_omega_excluded_at_let` run the
//! other edge: R5's looping term is in NO such candidate, at both new
//! constructors.
//!
//! **It is NOT the SN capstone, and the gap is not a matter of degree.**
//! `whnf_terminates_well_typed_dependent` is about `TypingCtx`, the dependent
//! TERM typing judgment. `WKC` is a SHAPE system — a kinding discipline whose
//! contexts carry `Sk`s, not types — so "every `WKC`-typed term's candidate
//! normalizes" is a statement about the type-level fragment and its
//! interpretation, not about every well-typed term of the kernel's theory.
//! Nothing here discharges `M : CandModel tenv`. What it does establish is the
//! property a `CandModel` instance would have to have, over a system that has
//! `const` and `let_`.
//!
//! ## B — the scope of every membership statement in R18-R23, computed
//!
//! **`r23_vcar_arr_is_top` is `Eq.refl`, and that is the point.** `vcarD` at an
//! ARROW shape DISCARDS its value:
//!
//! ```text
//! vcarD (Sk.arr d c) f e   reduces to   whnf_acc e,   for every f
//! ```
//!
//! So at an arrow shape a membership carries no information about the
//! interpretation at all. `r23_xval_members_sn` degenerates there to
//! `whnf_acc x → whnf_acc x`, and `r22_xval_conv` degenerates to the identity
//! function. The content of every membership-shaped result in R18-R23 lives at
//! `ty` and `kd` shapes, where — `r23_vcar_ty_is_the_set`, also `Eq.refl` — the
//! candidate IS the denoted set.
//!
//! Both halves are registered because the instrument should name the two states
//! apart. The negative control `r23_vcar_ty_collapse_probe` claims the arrow
//! collapse at `ty` for a general `C` and is REFUSED: if it were accepted,
//! every membership statement in this ladder would be the top candidate in
//! disguise and the normalization result would say nothing.
//!
//! **This does not weaken R22.** Conversion's job is to move a membership
//! between convertible terms, and at `ty` — where types live and where
//! conversion is used — it does exactly that. The arrow degeneracy is a fact
//! about `vcarD`'s definition (R12's), not a defect introduced here, and it was
//! true of `r16_val_conv` on the `sval` side all along. What is new is that it
//! is now written down.
//!
//! ## C — the drift check
//!
//! `r23_good_reproves_sval_good` states R12's `sval_good` and proves it from
//! this rung's native theorem through `r18_xval_sval`. Two genuinely different
//! proofs of one statement — R12's induction on `WK`, and an induction on `WKC`
//! pushed across the transfer — so a rung that widened the system while
//! drifting the adequacy statement would be invisible without it.
//!
//! ## What this rung does NOT do
//!
//! * **No SN capstone**, per §A above.
//! * **`proj` and `lit` are still untyped**, there is still no conversion RULE
//!   in `WKC`, and `konst` is still restricted to INERT constants.
//! * **The valuation premise is real.** Everything here is conditional on
//!   `GoodEnvD D r`, and `r23_good_no_env_probe` — which drops it — is refused.
//!   The unconditional instances are exactly the ones with a supplied good
//!   valuation, and the two `r12_junkEnv` witnesses are those.
//!
//! ## The named next item
//!
//! **The constant SHAPE ENVIRONMENT**, still — R22 named it and this rung
//! sharpens the price. `konst`'s arm here is `goodSet_whnfAcc` precisely
//! because an inert constant denotes the top candidate; under a `Name -> Sk`
//! environment it would denote a looked-up value, and the adequacy arm would
//! need that environment to be pointwise GOOD, which is a new hypothesis on
//! `the_red_env` rather than a lemma. That is the fourth `konst` arm in a row
//! this ladder has had for free, and the first one where it is visible what the
//! free ride was buying.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 10 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r23_src::{r23_items, R23Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R22's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R23 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r23_xval_good" => (
            &[
                "WKC.rec",
                "xval",
                "GoodD",
                "GoodEnvD",
                "goodSet_whnfAcc",
                "goodD_mkTyD",
                "isCandHI_piSet",
                "isCandHI_vcarD",
                "goodEnvD_vconsD",
                "goodD_junkD",
            ],
            "ADEQUACY at SEVEN constructors — R12's sval_good carried across. Every WKC \
             derivation's interpretation, at a GOOD valuation, is a GOOD value; GoodD is the \
             logical relation, candidacy of the denoted SET at ty and kd and the real \
             function-space clause at an arrow. konst is goodSet_whnfAcc and that is the whole \
             arm (an inert constant denotes the top candidate); let_ is the body's hypothesis at \
             the valuation extended by the VALUE's interpretation, with goodEnvD_vconsD supplying \
             the extension's goodness from the value's own hypothesis.",
        ),
        "r23_isCandHI_xval" => (
            &["r23_xval_good", "isCandHI_vcarD"],
            "The SET a WKC-typed term denotes is a CANDIDATE.",
        ),
        "r23_xval_members_sn" => (
            &["r23_isCandHI_xval", "isCandHI_cr1", "whnf_acc"],
            "NORMALIZATION: every member of the candidate a WKC-typed term denotes is whnf_acc — \
             accessible under whnf_step, hence with no infinite reduction sequence. \
             UNCONDITIONAL: no CandModel hypothesis anywhere in its closure. NOT the SN capstone: \
             whnf_terminates_well_typed_dependent is about TypingCtx, the dependent TERM judgment, \
             where WKC is a SHAPE system whose contexts carry Sk's and not types.",
        ),
        "r23_xval_excludes_omega" => (
            &["r23_xval_members_sn", "r5_omegaV_not_whnfAcc"],
            "R5's looping term is in NO such candidate. The edge that keeps the normalization \
             theorem from being about an empty or a too-large set.",
        ),
        "r23_good_reproves_sval_good" => (
            &["r23_xval_good", "r18_xval_sval", "Eq.substType"],
            "THE DRIFT CHECK: R12's sval_good STATEMENT re-proved from R23's native theorem \
             through R18's transfer. Two genuinely different proofs of one statement — R12's \
             induction on WK, and an induction on WKC pushed across the transfer.",
        ),
        "r23_sn_fires_at_konst" => (
            &["r23_xval_members_sn", "r17_konst_mem_witness", "r17_konst_witness"],
            "THE THEOREM CONCLUDING, AT A REAL OBJECT. R17's r17_konst_mem_witness is an \
             inhabitant of the candidate its konst witness denotes; fed to r23_xval_members_sn it \
             yields whnf_acc of that constant. So the candidate is INHABITED and the theorem \
             FIRES, which is what separates a normalization result from a vacuous one.",
        ),
        "r23_omega_excluded_at_konst" => (
            &["r23_xval_excludes_omega", "r17_konst_witness", "goodEnvD_junk"],
            "Omega is not in the candidate R17's konst witness denotes.",
        ),
        "r23_omega_excluded_at_let" => (
            &["r23_xval_excludes_omega", "r17_let_witness", "goodEnvD_junk"],
            "The same at R17's let_ witness — the exclusion at both new constructors.",
        ),
        "r23_vcar_arr_is_top" => (
            &["vcarD", "Eq.refl", "whnf_acc"],
            "THE SCOPE OF EVERY MEMBERSHIP STATEMENT IN R18-R23, COMPUTED. vcarD at an ARROW shape \
             DISCARDS its value and returns the top candidate, for every f. Eq.refl proves it, \
             which is the point — it is a computation, not a theorem. So at an arrow shape \
             r23_xval_members_sn degenerates to whnf_acc x -> whnf_acc x and r22_xval_conv \
             degenerates to the identity; the content lives at ty and kd shapes. A fact about \
             R12's vcarD, true of r16_val_conv on the sval side all along, and new only in being \
             written down.",
        ),
        "r23_vcar_ty_is_the_set" => (
            &["vcarD", "Eq.refl"],
            "The other half, also Eq.refl: at ty the candidate IS the denoted set, so nothing is \
             discarded there. Registered beside its sibling so the instrument names the two states \
             apart. Controlled by r23_vcar_ty_collapse_probe, which claims the arrow collapse at \
             ty and is REFUSED.",
        ),
        _ => (
            &[],
            "R23 adequacy and normalization: GoodD of every xval, and whnf_acc of every member.",
        ),
    }
}

impl Specification {
    /// Register R23: adequacy and normalization at seven constructors.
    pub(super) fn add_candmodel_construct_r23(&mut self) -> Result<(), SpecError> {
        for item in r23_items() {
            match item {
                R23Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r23_tests.rs"]
mod tests;
