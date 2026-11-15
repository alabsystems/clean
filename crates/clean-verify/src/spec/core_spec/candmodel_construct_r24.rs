// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R24 of the candidate-model construction ladder — **THE REDUCIBILITY
//! INTERFACE**: reducibility at a `ty`-shaped type over R17's seven-constructor
//! interpretation, R1's β head-expansion engine landed on it, and R1's ζ
//! refutation paired beside it in one constant.
//!
//! ## Why this rung exists, and what it corrects
//!
//! R18-R23 built the semantic stack and then adequacy and normalization over
//! R17's seven-constructor system. The obvious next question is the Tait
//! FUNDAMENTAL THEOREM — `Γ ⊢ t : A ⟹ t` reducible at `A` — and the obvious
//! first question about that is whether its `lam` case has an engine.
//!
//! **It does, and this rung lands it.** `r24_red_beta_expand` is R1's
//! `candExpHF_beta` instantiated at the candidates R23 supplies. The reason it
//! works is R1's own pivot, and it is worth restating because it is easy to get
//! backwards: the spec's `Neutral` sends every `app` head to `ConstFreeUnit`,
//! so `app (lam ty b) a` IS neutral and cr3 applies. A β redex is also
//! `HeadFree` — its `kapp_fn` is a `lam`, whose `kexpr_const_name` is `none` —
//! so the HeadFree-restricted class is enough, and `isCandHI_weaken` is the one
//! step from what R23 proves to what R1's engine wants.
//!
//! ## A — the ζ contrast, and why it is in the same constant
//!
//! The contrast was meant to be ONE constant — an `AndType` pairing the β
//! engine with `zeta_expansion_not_generic`, R1's proof that the SAME engine
//! shape with the redex swapped to `let_ ty a b` implies `Empty`. **It does not
//! typecheck, and the reason is measured rather than guessed:** `GoodEnvD`
//! lives in `Type 1` — it quantifies over `GoodD`, which R12 put there
//! deliberately because this kernel is NON-CUMULATIVE and `IsCandHI S : Type 0`
//! could not be the base — so the β-engine statement is a `Type 1` while
//! `AndType` is `Type 0`-valued. The kernel says `universe level conflict:
//! 1 vs 0`, and the spec has no `Type 1` conjunction.
//!
//! So the contrast is carried MECHANICALLY, by three things that do hold:
//! `r24_red_beta_expand` is registered, `zeta_expansion_not_generic` is R1's
//! and registered, and `r24_zeta_engine_probe` — the same engine at
//! `r24_RedAt` with the redex swapped — is REFUSED by the kernel. A drift guard
//! pins the remaining half, that the two engine SHAPES differ in exactly the
//! redex and share every premise, which is what makes the refutation bear on
//! this engine at all.
//!
//! The pairing matters deliberately. R17 added `let_` to the shape system and
//! R18-R23 carried weakening, substitution, instantiation, β, step, conversion,
//! adequacy and normalization over it without `let_` ever costing more than a
//! congruence. It would be easy to read the ladder as having made `let_` as
//! tractable as `lam`. It has not, and the obstruction is structural rather
//! than a matter of effort: `Neutral (let_ …)` is `Empty`, so cr3 never reaches
//! a ζ redex, and R1 exhibits a genuine candidate set containing a
//! let-contractum while EXCLUDING its redex.
//!
//! `r24_zeta_engine_probe` is the machine-visible half: the ζ engine stated at
//! `r24_RedAt` and proved the way the β one is. The kernel refuses it.
//!
//! **What that means for a fundamental theorem over this system.** Its `lam`
//! case is supplied. A `let_` case is NOT, and cannot be by any per-set
//! argument. The honest options are to restrict the term judgment to ζ-free
//! terms, or to carry `whnfAcc_zeta_expand` — which holds only at the base
//! whole-SN set — as an explicit hypothesis. Those differ in what the resulting
//! theorem may claim, and this rung deliberately does not choose: it makes the
//! choice visible instead of burying it in a `let_` arm.
//!
//! ## B — `Sk.ty` is where the interface is faithful
//!
//! R23 measured that `vcarD` at an ARROW shape discards its value, so every
//! membership-shaped result degenerates there. `r24_RedAt` is defined at
//! `Sk.ty` only, which is exactly where `r23_vcar_ty_is_the_set` says the
//! candidate IS the denoted set. That is not a restriction added for
//! convenience — it is where terms live, `WKC` being a system that types the
//! TYPE level.
//!
//! `r24_red_conv_stable` is registered separately for the same reason: it is
//! R22's conversion lemma at `Sk.ty`, the instance that does NOT degenerate,
//! and the one a conversion rule in a term judgment would consume.
//!
//! ## What this rung does NOT do
//!
//! * **There is still no term typing judgment on this lineage, and that is now
//!   the whole gap.** R6 has one (`SynTy`) with a Tait fundamental theorem
//!   (`synTy_fundamental`), but over `candInterp`, which R11 PROVED is not
//!   conversion-invariant — which is why R12 moved to the `WK`/`sval` lineage
//!   in the first place. So the two halves exist in different lineages: R6 has
//!   the judgment and the tower, R12-R24 has the metatheory and now the
//!   interface. Porting the first onto the second is the named next item.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//! * **Everything is conditional on `GoodEnvD`**, and
//!   `r24_candhf_no_env_probe` — which drops it — is refused.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 1 `add_recursive_def` and 5
//! value-bearing theorems through `add_definition` with kernel `add_decl`
//! checking.

use std::collections::HashSet;

use super::candmodel_construct_r24_src::{r24_items, R24Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R23's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R24 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r24_RedAt" => (
            &["vcarD", "xval", "WKC"],
            "REDUCIBILITY AT A TYPE: a term is reducible at A when it belongs to the candidate A \
             denotes. A is required WKC-typed at shape Sk.ty, which is exactly where vcarD is \
             faithful (r23_vcar_ty_is_the_set) — unlike the arrow-shaped instances R23 measured, \
             this predicate carries the interpretation's full content. Not a convenience \
             restriction: Sk.ty is where terms live, WKC being a system that types the TYPE level.",
        ),
        "r24_red_isCandHF" => (
            &["r23_isCandHI_xval", "isCandHI_weaken", "r24_RedAt"],
            "Reducibility at a type is a HEAD-FREE candidate. R23 gives IsCandHI; isCandHI_weaken \
             is the one step to the class R1's engines are stated over.",
        ),
        "r24_red_beta_expand" => (
            &["candExpHF_beta", "r24_red_isCandHF", "r24_RedAt"],
            "BETA HEAD-EXPANSION at r24_RedAt — R1's candExpHF_beta instantiated at the candidates \
             R23 supplies, and the lemma a Tait fundamental theorem spends at its lam case. It \
             exists BECAUSE a beta redex is NEUTRAL: the spec's Neutral sends every app head to \
             ConstFreeUnit, so app (lam ty b) a is neutral and cr3 applies. It is also HeadFree \
             (its kapp_fn is a lam, whose kexpr_const_name is none), which is why the \
             HeadFree-restricted class suffices.",
        ),
        "r24_red_members_sn" => (
            &["r23_xval_members_sn", "r24_RedAt"],
            "Every reducible term is whnf_acc — R23's normalization theorem at Sk.ty, which is its \
             non-degenerate shape.",
        ),
        "r24_red_excludes_omega" => (
            &["r23_xval_excludes_omega", "r24_RedAt"],
            "The looping term is reducible at NO type.",
        ),
        "r24_red_conv_stable" => (
            &["r22_xval_conv", "r24_RedAt"],
            "Reducibility is stable under CONVERSION of the type — R22's val_conv at Sk.ty. \
             Registered separately because R23 measured that r22_xval_conv degenerates to the \
             identity at ARROW shapes; this is the instance where it does not, and the one a \
             conversion rule in a term judgment would consume.",
        ),
        _ => (
            &[],
            "R24 reducibility interface: RedAt, the beta engine on it, and the zeta contrast.",
        ),
    }
}

impl Specification {
    /// Register R24: the reducibility interface.
    pub(super) fn add_candmodel_construct_r24(&mut self) -> Result<(), SpecError> {
        for item in r24_items() {
            match item {
                R24Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R24Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r24_tests.rs"]
mod tests;
