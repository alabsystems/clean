// Copyright 2026 Andrew Yates.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypothesis-free Church-Rosser over the concrete `faithful_red_env`
//! (#2859, real-env confluence discharge).
//!
//! Every confluence result in the tree — `par_reduces_p_star_diamond`,
//! `par_reduces_c_star_diamond` (par_reduces_p_topdev.rs) — is the Takahashi /
//! Tait-Martin-Löf multi-step diamond, but each carries the FOUR faithful
//! RecEnv interfaces as HYPOTHESES:
//!
//! ```text
//! forall (env : RecEnv), RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env ->
//!   RecEnvClosed env -> RecEnvLiftClosed env -> ... -> par_strips_witness_*_star env e1 e2
//! ```
//!
//! `faithful_red_env` (faithful_red_env.rs) is a CONCRETE, deliberately
//! non-vacuous `RedEnv` (one real recursor rule + one real definition, both with
//! the closed-lambda rhs `LAM`) for which all four interfaces are discharged as
//! genuine `DerivedProved` terms:
//!
//!   - i1 `faithful_red_env_reduct_not_redex` : `RecEnvReductNotRedex (red_rec faithful_red_env)`
//!   - i2 `faithful_rec_env_ctor_no_recmeta`  : `RecEnvCtorNoRecMeta   (red_rec faithful_red_env)`
//!   - i3 `faithful_rec_env_closed`           : `RecEnvClosed          (red_rec faithful_red_env)`
//!   - i4 `faithful_rec_env_lift_closed`      : `RecEnvLiftClosed      (red_rec faithful_red_env)`
//!
//! This module composes the two — instantiating the generic star-diamonds at
//! `env := red_rec faithful_red_env` and feeding the four honest witnesses — to
//! obtain the FIRST fully-UNCONDITIONAL (hypothesis-free) confluence statements
//! in the tree:
//!
//!   - `par_reduces_c_star_diamond_faithful` — Church-Rosser of `par_reduces_c_star`
//!     over the real env (the relation `par_reduces_c_star_diamond` describes as
//!     "the result that makes `church_rosser_whnf` deletable"); now with NO
//!     interface hypotheses.
//!   - `par_reduces_p_star_diamond_faithful` — the direct proper-parallel
//!     (Takahashi) Church-Rosser over the real env.
//!
//! These are the real-env EXISTENCE proof that the four-interface
//! parameterization is simultaneously dischargeable by a non-vacuous env — i.e.
//! the confluence machinery is not secretly parameterized on an undischargeable
//! (or contradictory) hypothesis bundle. A capstone brick on the
//! `church_rosser_whnf` frontier.
//!
//! Both are pure applications: no new recursion, `DerivedProved`, zero
//! `axiom_deps` (the star-diamonds and all four witnesses are themselves
//! `DerivedProved`). Runs AFTER `add_faithful_red_env_bundle` (all four
//! witnesses in scope) and `add_par_reduces_p_topdev` (both star-diamonds in
//! scope). Strategy guide: the Aristotle `par_star_confluent`
//! (`proofs/lean-aristotle/Confluence.lean`) triangle -> diamond -> strip ->
//! star closure, whose Clean port (`dev_triangle` -> `par_diamond` ->
//! `par_strips_p_star_strip` -> `par_reduces_p_star_diamond`) this brick caps
//! with the concrete-env discharge.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the hypothesis-free Church-Rosser corollaries over the concrete
    /// `faithful_red_env`. See the module docs for the discharge structure.
    pub(super) fn add_faithful_confluence(&mut self) -> Result<(), SpecError> {
        // par_reduces_c_star_diamond_faithful: the four-interface hypotheses of
        // par_reduces_c_star_diamond discharged at env := red_rec faithful_red_env
        // with the four honest DerivedProved witnesses. UNCONDITIONAL confluence
        // of par_reduces_c_star over the real env.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_diamond_faithful".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_c_star (red_rec faithful_red_env) e e1 -> ",
                "par_reduces_c_star (red_rec faithful_red_env) e e2 -> ",
                "par_strips_witness_c_star (red_rec faithful_red_env) e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_c_star (red_rec faithful_red_env) e e1) ",
                    "(h2 : par_reduces_c_star (red_rec faithful_red_env) e e2) => ",
                    "par_reduces_c_star_diamond (red_rec faithful_red_env) e e1 e2 ",
                    "faithful_red_env_reduct_not_redex ",
                    "faithful_rec_env_ctor_no_recmeta ",
                    "faithful_rec_env_closed ",
                    "faithful_rec_env_lift_closed ",
                    "h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "UNCONDITIONAL Church-Rosser of par_reduces_c_star over the concrete faithful_red_env: two ",
                "computational-parallel multi-step reductions from a common source join at a shared reduct, ",
                "with NO interface hypotheses. par_reduces_c_star_diamond (the relation that makes ",
                "church_rosser_whnf deletable) instantiated at env := red_rec faithful_red_env, with its four ",
                "faithful interfaces discharged by the honest DerivedProved witnesses ",
                "faithful_red_env_reduct_not_redex (i1), faithful_rec_env_ctor_no_recmeta (i2), ",
                "faithful_rec_env_closed (i3), faithful_rec_env_lift_closed (i4). The real-env existence proof ",
                "that the four-interface parameterization is simultaneously dischargeable by a non-vacuous env. ",
                "Pure application, DerivedProved, zero axiom_deps. Part of #2859 (real-env confluence discharge)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_diamond".to_string(),
                "par_strips_witness_c_star".to_string(),
                "red_rec".to_string(),
                "faithful_red_env".to_string(),
                "faithful_red_env_reduct_not_redex".to_string(),
                "faithful_rec_env_ctor_no_recmeta".to_string(),
                "faithful_rec_env_closed".to_string(),
                "faithful_rec_env_lift_closed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_diamond_faithful: the direct proper-parallel
        // (Takahashi) confluence, same discharge at env := red_rec faithful_red_env.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_diamond_faithful".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_p_star (red_rec faithful_red_env) e e1 -> ",
                "par_reduces_p_star (red_rec faithful_red_env) e e2 -> ",
                "par_strips_witness_p_star (red_rec faithful_red_env) e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_p_star (red_rec faithful_red_env) e e1) ",
                    "(h2 : par_reduces_p_star (red_rec faithful_red_env) e e2) => ",
                    "par_reduces_p_star_diamond (red_rec faithful_red_env) e e1 e2 ",
                    "faithful_red_env_reduct_not_redex ",
                    "faithful_rec_env_ctor_no_recmeta ",
                    "faithful_rec_env_closed ",
                    "faithful_rec_env_lift_closed ",
                    "h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "UNCONDITIONAL Church-Rosser of par_reduces_p_star (proper Takahashi parallel reduction) over ",
                "the concrete faithful_red_env: two proper-parallel multi-step reductions from a common source ",
                "join at a shared reduct, with NO interface hypotheses. par_reduces_p_star_diamond instantiated ",
                "at env := red_rec faithful_red_env, with its four faithful interfaces discharged by the honest ",
                "DerivedProved witnesses (i1..i4). The direct real-env analogue of the Aristotle par_star_confluent ",
                "strategy guide. Pure application, DerivedProved, zero axiom_deps. Part of #2859 (real-env ",
                "confluence discharge)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star_diamond".to_string(),
                "par_strips_witness_p_star".to_string(),
                "red_rec".to_string(),
                "faithful_red_env".to_string(),
                "faithful_red_env_reduct_not_redex".to_string(),
                "faithful_rec_env_ctor_no_recmeta".to_string(),
                "faithful_rec_env_closed".to_string(),
                "faithful_rec_env_lift_closed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "faithful_confluence_tests.rs"]
mod faithful_confluence_tests;
