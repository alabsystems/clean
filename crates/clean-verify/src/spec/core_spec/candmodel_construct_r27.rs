// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R27 of the candidate-model construction ladder — **VARIABLES ARE
//! REDUCIBLE**, and reducibility is derivation-irrelevant.
//!
//! ## Why this rung
//!
//! R26 closed by saying what remained was "the JUDGMENT, not a lemma". That is
//! true of the RULES — `r25_red_app` and `r26_red_lam_one` are the `app` and
//! `lam` cases — but writing the judgment's fundamental theorem turns up two
//! obligations that are about `r24_RedAt` ITSELF rather than about any rule,
//! and neither existed. This rung is those two.
//!
//! ## A — derivation irrelevance, and why the theorem cannot be stated without it
//!
//! `r24_RedAt D A hA r t` mentions a `WKC` derivation `hA`. A fundamental
//! theorem's arms each have a derivation in hand — `tvar` has the context's,
//! `tapp` and `tlam` have the ones their nodes carry — and NONE of them is the
//! derivation the statement was handed. So the statement cannot be uniform
//! unless the predicate is insensitive to which one is used.
//!
//! **`r27_red_irrel`** is that fact, and it costs one `Eq.substType`:
//! `r17_xval_irrel` (R17's subsingleton, through `r17_wkc_deriv_unique`) equates
//! the interpretations, and `vcarD Sk.ty V` computes to `V`. This is the
//! subsingleton's fifth consumer outside R17.
//!
//! ## B — variables are reducible, and why that is the pivot
//!
//! **`r27_red_var`**: every de Bruijn variable is reducible at EVERY type.
//! Three ingredients, all already in the tree:
//!
//! | obligation | discharged by |
//! |---|---|
//! | `bvar i` is Neutral | `ConstFreeUnit.triv` — the spec's `Neutral` sends a `bvar` there |
//! | `bvar i` is `HeadFree` | `Eq.refl` — `kapp_fn (bvar i)` is `bvar i`, whose `kexpr_const_name` is `none` |
//! | every reduct of `bvar i` is reducible | vacuous — `r15_whnf_stepT_inv` at a `bvar` head has NO continuations |
//!
//! cr3 then applies. **This is the classical pivot of a Tait argument and the
//! reason the `lam` case can close at all.** That case must hand R1's engine
//! `whnf_acc` of the substituted body, but the body is only reducible once an
//! argument has been substituted into it; the classical escape is to substitute
//! a VARIABLE, which is sound exactly because variables are reducible.
//!
//! **The neutrality premise is load-bearing, and that is pinned.**
//! `r27_lam_reducible_probe` runs the identical cr3 route at a LAMBDA and the
//! kernel refuses it — the spec's `Neutral` sends a `lam` to `Empty`, so
//! `ConstFreeUnit.triv` cannot discharge it. If that probe ever passed,
//! `r24_RedAt` would be total and every membership result in R18-R26 would be
//! worthless, so it is the sharpest control this rung can carry.
//!
//! ## What this rung does NOT do
//!
//! * **Still no term judgment.** R27 supplies the two `RedAt`-level facts the
//!   fundamental theorem needs; the judgment and the theorem itself remain
//!   unwritten. What is now in hand for them: `tvar` ← `r27_red_var` +
//!   `r27_red_irrel`, `tapp` ← `r25_red_app`, `lam` ← `r26_red_lam_one` +
//!   `r26_lam_premise_is_the_induction_hypothesis`, with `r27_red_var_is_sn`
//!   for the engine's `whnf_acc` premises.
//! * **The fragment is unchanged**: ζ-free and non-dependent, for the reasons
//!   R24 and R25 record.
//! * **No SN capstone.** Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## Census
//!
//! ZERO new axioms and ZERO new inductives: 3 value-bearing theorems through
//! `add_definition` with kernel `add_decl` checking.

use std::collections::HashSet;

use super::candmodel_construct_r27_src::{r27_items, R27Item};
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R26's theorem helper, verbatim.
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

/// `(dependencies, description)` for every R27 constant, one row each.
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "r27_red_irrel" => (
            &["r17_xval_irrel", "r24_RedAt", "Eq.substType"],
            "REDUCIBILITY IS DERIVATION-IRRELEVANT. r24_RedAt mentions a WKC derivation, and a \
             fundamental theorem's arms each hold a DIFFERENT one from the one its statement was \
             handed — tvar the context's, tapp and tlam their nodes' — so the statement cannot be \
             uniform without this. One Eq.substType off r17_xval_irrel, the subsingleton's fifth \
             consumer outside R17.",
        ),
        "r27_red_var" => (
            &[
                "isCandHF_cr3",
                "r24_red_isCandHF",
                "r15_whnf_stepT_inv",
                "Neutral",
                "ConstFreeUnit.triv",
            ],
            "VARIABLES ARE REDUCIBLE at EVERY type — the classical pivot of a Tait argument. \
             bvar i is Neutral (the spec's Neutral sends a bvar to ConstFreeUnit), is HeadFree \
             (kapp_fn of a bvar is itself, whose kexpr_const_name is none), and CANNOT STEP \
             (r15_whnf_stepT_inv at a bvar head has no continuations), so cr3 applies with a \
             vacuous reduct premise. It is what lets the lam case close: that case must hand R1's \
             engine whnf_acc of the substituted body, the body is only reducible once an argument \
             is substituted, and the classical escape is to substitute a VARIABLE. Controlled by \
             r27_lam_reducible_probe, which runs the identical route at a LAMBDA and is REFUSED \
             because Neutral sends a lam to Empty.",
        ),
        "r27_red_var_is_sn" => (
            &["r27_red_var", "r24_red_members_sn"],
            "The immediate corollary and the shape the lam case consumes: a variable normalizes. \
             The smallest object at which the whole chain from R23's adequacy down to a concrete \
             term is visible.",
        ),
        _ => (
            &[],
            "R27 reducibility toolkit: variables are reducible, and RedAt is derivation-irrelevant.",
        ),
    }
}

impl Specification {
    /// Register R27: the two `RedAt`-level facts a fundamental theorem needs.
    pub(super) fn add_candmodel_construct_r27(&mut self) -> Result<(), SpecError> {
        for item in r27_items() {
            match item {
                R27Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r27_tests.rs"]
mod tests;
