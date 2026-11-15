// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R26 of the candidate-model construction ladder — **THE SINGLE-CONTRACTUM
//! ENGINE**, ported to the HeadFree candidate class, and the `lam` rule in the
//! form a fundamental theorem actually supplies it.
//!
//! ## Why this rung
//!
//! R25 landed both semantic rules of a Tait fundamental theorem, but its `lam`
//! rule takes R1's FAMILY premise — the contractum's membership for every
//! `betaStar`-development of the body. That is R1's honest engine interface and
//! it is not what a fundamental theorem's `lam` case produces. That case
//! produces the SINGLE contractum.
//!
//! R2 already bridges those: `candExp_beta_subst` manufactures the family from
//! the single contractum by walking `betaStar` with `candSet_betaStar_closed`
//! and `betaStar_inst_transport`. It could not be used here, and the reason was
//! narrow and precise — it requires `IsCandSet` (UNRESTRICTED cr3) where R23's
//! adequacy yields `IsCandHI`, which weakens to `IsCandHF` and no further, and
//! **no `candExpHF_beta_subst` existed**.
//!
//! ## A — the port, and why it is mechanical
//!
//! `candSet_betaStar_closed`'s own description says it iterates "the **cr2**
//! face", and cr2 is UNRESTRICTED in both classes — only cr3 differs, by taking
//! a `HeadFree` witness. So `r26_candHF_betaStar_closed` is R2's term with
//! `IsCandSet` replaced by `IsCandHF` and `isCandSet_cr2` by `isCandHF_cr2`.
//! That is exactly the weakening R5 applied to `candExp_beta` to obtain
//! `candExpHF_beta`, and `r26_candExpHF_beta_subst` is then R2's proof with two
//! names changed.
//!
//! **The claim that it is only the cr2 face is pinned, not repeated.**
//! `r26_star_cr1_probe` swaps cr2 for cr1 and the kernel refuses it: cr1 says
//! members are `whnf_acc`, which does not move membership along a step, and the
//! walk is the only thing that turns a single contractum into R1's family.
//!
//! ## B — the rule, and the bridge to an induction hypothesis
//!
//! `r26_red_lam_one` is R25's `lam` rule taking the single contractum, through
//! the same `r20_xval_lift0` transport.
//!
//! `r26_lam_premise_is_the_induction_hypothesis` is the half-line that makes it
//! usable, and it is worth having as a constant rather than as a remark.
//! `psubst_scons_instantiate` (already in the tree, DerivedProved, zero
//! `axiom_deps`) says
//!
//! ```text
//! psubst (scons a s) b  =  instantiate (psubst (up s) b) a
//! ```
//!
//! so the premise `r26_red_lam_one` wants — reducibility of
//! `instantiate (psubst (up s) b) a` — IS reducibility of
//! `psubst (scons a s) b`, which is precisely what an induction on a term
//! judgment hands back at its `lam` case.
//!
//! ## C — what a fundamental theorem now needs, and what it does not
//!
//! With this rung the three cases of a Tait fundamental theorem over the
//! `WKC`/`xval` lineage have their semantic counterparts:
//!
//! | case | supplied by |
//! |---|---|
//! | `var` | the reducible-substitution hypothesis (part of the statement) |
//! | `app` | `r25_red_app` |
//! | `lam` | `r26_red_lam_one` + `r26_lam_premise_is_the_induction_hypothesis` |
//!
//! **What remains is the JUDGMENT, not a lemma.** Writing it needs a term
//! context of TYPES with lifting under binders, and its statement needs a
//! reducible-substitution predicate. Neither is hard; neither is here.
//!
//! **`RecEnvClosed (red_rec the_red_env)` is carried, not discharged.**
//! `betaStar_inst_transport` takes it, the spec passes it as a premise in
//! dozens of places rather than proving it at `the_red_env`, and so every
//! constant in Group B carries it explicitly. `r26_one_no_recenv_probe` drops
//! it and is refused. A fundamental theorem built on this would carry it too,
//! and should say so.
//!
//! ## What this rung does NOT do
//!
//! * **The fragment is unchanged**: ζ-free (R24's contrast — no per-set engine
//!   reaches `let_`) and NON-DEPENDENT (R17's `piShape` erasure, visible in
//!   `r25_arrow`'s lift).
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!   A fundamental theorem for this fragment would not either — see
//!   `docs/issues/2026-09-17-fundamental-theorem-route-on-the-wkc-lineage.md`
//!   §4, which states what would still not follow.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 5 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r26_src::{r26_items, R26Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R25's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R26 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r26_candHF_betaStar_closed" => (
            &["betaStar.rec", "isCandHF_cr2", "whnf_step.beta"],
            "R2's candSet_betaStar_closed at the HEADFREE class. R2's proof iterates the cr2 face \
             and nothing else — its own description says so — and cr2 is UNRESTRICTED in both \
             IsCandSet and IsCandHF; only cr3 differs, by taking a HeadFree witness. So this is \
             R2's term with two names changed, the same weakening R5 applied to candExp_beta to \
             get candExpHF_beta. Pinned by r26_star_cr1_probe, which swaps cr2 for cr1 and is \
             REFUSED.",
        ),
        "r26_candExpHF_beta_subst" => (
            &[
                "candExpHF_beta",
                "r26_candHF_betaStar_closed",
                "betaStar_inst_transport",
                "RecEnvClosed",
            ],
            "THE CONSTANT THE LADDER WAS MISSING: R2's single-contractum engine at the HeadFree \
             class. R1's engine takes a FAMILY premise (the contractum for every \
             betaStar-development of the body), which is the honest interface but NOT what a \
             fundamental theorem's lam case produces; that case produces the SINGLE contractum. R2 \
             manufactures the family from it by walking betaStar, and every piece of that walk has \
             a HeadFree counterpart. Carries RecEnvClosed (red_rec the_red_env), which the spec \
             passes as a premise rather than discharging.",
        ),
        "r26_red_beta_expand_one" => (
            &["r26_candExpHF_beta_subst", "r24_red_isCandHF", "r24_RedAt"],
            "Beta head-expansion at r24_RedAt from the SINGLE contractum — the single-contractum \
             engine instantiated at the candidates R23 supplies.",
        ),
        "r26_red_lam_one" => (
            &["r26_red_beta_expand_one", "r20_xval_lift0", "r25_arrowWkc", "Eq.substType"],
            "THE lam RULE IN THE FORM A FUNDAMENTAL THEOREM SUPPLIES IT. R25's r25_red_lam takes \
             R1's family premise; this takes the single contractum, through the same \
             r20_xval_lift0 transport.",
        ),
        "r26_lam_premise_is_the_induction_hypothesis" => (
            &["psubst_scons_instantiate", "r24_RedAt", "Eq.substType"],
            "THE BRIDGE, as a constant rather than a remark. psubst_scons_instantiate says \
             psubst (scons a s) b = instantiate (psubst (up s) b) a, so the premise r26_red_lam_one \
             wants IS reducibility of psubst (scons a s) b — precisely what an induction on a term \
             judgment hands back at its lam case. With this, a Tait fundamental theorem's three \
             cases all have semantic counterparts and what remains is the JUDGMENT, not a lemma.",
        ),
        _ => (
            &[],
            "R26 single-contractum engine: the HeadFree port and the lam rule it enables.",
        ),
    }
}

impl Specification {
    /// Register R26: the single-contractum engine at the HeadFree class.
    pub(super) fn add_candmodel_construct_r26(&mut self) -> Result<(), SpecError> {
        for item in r26_items() {
            match item {
                R26Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r26_tests.rs"]
mod tests;
