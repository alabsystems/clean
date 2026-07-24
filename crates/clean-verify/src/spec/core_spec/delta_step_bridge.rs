// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Delta faithful-interface mirror of `iota_step_bridge` (church_rosser_whnf
//! retirement track, design `scratch/defeq-family-redefinition-design.md` §3/§4).
//!
//! `delta_reduces.mk` requires the reduct to be DefEq to the redex (`h_subst`) and
//! type-preserving (`h_fwd`/`h_bwd`). With the opaque `DefEnv` unfolding values
//! those facts are NOT derivable from `delta_step` alone — they hold only when each
//! definition's unfolding value genuinely computes a faithful reduct. That
//! guarantee is the `DefEnvWellformed` predicate: a real inductive (proper
//! recursor, NOT an axiom) carrying the three universally-quantified faithfulness
//! facts over the env's δ steps — the δ analogue of `RecEnvWellformed`
//! (`iota_step_bridge.rs:44`). It is NOT an axiom: it is a *defined* HYPOTHESIS
//! whose witness, for the kernel's actual definition environment, is discharged
//! constructively at the end of the track by modeling `defval_for` — exactly the
//! posture of every other interface in the Hindley-Rosen assembly
//! (`RecEnvWellformed`, `RecEnvDefEnvDisjoint`, `DefEnvClosed`, `i1..i8`).
//!
//! Indexed by `RedEnv` (reading `red_def env`) so it is uniform with the combined
//! reduction environment the δ-extended development already threads (the bound
//! `(env : RedEnv)` carried-hypothesis pattern — NOT a `forall env` over the
//! family, NOT a postulated env constant).
//!
//! `delta_step_to_reduces` is the δ analogue of `iota_step_to_reduces`: given the
//! env is wellformed, a computational δ step yields an abstract `delta_reduces`
//! witness (project the three faithfulness facts via `DefEnvWellformed.rec`, apply
//! `delta_reduces.mk`). This is single-step δ subject reduction + subst-DefEq, a
//! standard preservation fact STRICTLY WEAKER than confluence — it does NOT encode
//! "any two reductions join". It is the honest home for the three fields the loose
//! `delta_reduces.mk` used to bundle as undischarged constructor arguments.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The DefEq-faithfulness fact carried by `DefEnvWellformed env`: every δ step in
/// the env's definition environment yields a reduct DefEq to the redex under any
/// instantiation. The δ analogue of `WF_SUBST` (`iota_step_bridge.rs:33`).
const DEF_WF_SUBST: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
/// The forward type-preservation fact for δ steps.
const DEF_WF_FWD: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
/// The backward type-preservation fact for δ steps.
const DEF_WF_BWD: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

impl Specification {
    pub(super) fn add_delta_step_bridge(&mut self) -> Result<(), SpecError> {
        // DefEnvWellformed env: the faithful-interface predicate. A real inductive
        // (proper recursor, not an axiom projector) carrying the three facts
        // delta_reduces.mk needs, universally over the env's delta steps. The δ
        // analogue of RecEnvWellformed; indexed by RedEnv, reading red_def env.
        self.add_inductive(
            &format!(
                "inductive DefEnvWellformed (env : RedEnv) : Type\n| mk : ({DEF_WF_SUBST}) → ({DEF_WF_FWD}) → ({DEF_WF_BWD}) → DefEnvWellformed env"
            ),
            "Faithfulness interface for a definition environment (the δ mirror of RecEnvWellformed): \
             every computational delta_step (red_def env) yields a DefEq-to-redex (h_subst) and \
             bidirectional typing transfer (h_fwd/h_bwd). A defined HYPOTHESIS (NOT an axiom); its \
             witness for the kernel definition env is discharged at the end of the track by modeling \
             defval_for. Carries single-step delta subject reduction + subst-DefEq — strictly weaker \
             than confluence, NOT a join claim. Part of the church_rosser_whnf retirement track.",
        )?;

        // delta_step_to_reduces: the FORWARD bridge, simplified for the tightened
        // family. The ctor now carries the step itself, so the bridge just wraps it
        // (no DefEnvWellformed projection — the three faithfulness facts moved to the
        // transport lemmas). Env pinned to the fixed the_red_env (NOT forall env).
        self.add_definition(SpecDefinition {
            name: "delta_step_to_reduces".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "delta_step (red_def the_red_env) e e' -> delta_reduces e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(h : delta_step (red_def the_red_env) e e') => ",
                    "delta_reduces.mk e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Forward bridge: a computational delta_step over the fixed the_red_env yields an abstract ",
                "delta_reduces witness (just apply the tightened delta_reduces.mk to the step). Env pinned ",
                "to the_red_env. DerivedProved; the only axiom dep is delta_reduces itself (a FoundationalRule ",
                "family it constructs). Part of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduces.mk".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::from(["delta_reduces".to_string()]),
        })?;

        // delta_reduces_to_step: the REVERSE bridge — VALID because the tightened
        // family's sole inhabitant IS a step. Project the lone field via
        // delta_reduces.rec. Since delta_reduces is now a GENUINE inductive (Brick
        // R2), delta_reduces.rec is the KERNEL-GENERATED recursor in the
        // PROMOTED-PARAMETER (AndType) shape: the e/e' indices are IMPLICIT params,
        // the motive ranges over the major premise only, and the single minor has
        // no index binders — so the recursor takes just (motive, minor, major) with
        // e/e' inferred (NOT the retired hand-axiom's 3-ary index-motive shape).
        // Total function, NOT ex-falso. The δ engine of def_eq_joinable's delta arm.
        self.add_definition(SpecDefinition {
            name: "delta_reduces_to_step".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "delta_reduces e e' -> delta_step (red_def the_red_env) e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : delta_reduces e e') => ",
                    "delta_reduces.rec ",
                    "(fun (_ : delta_reduces e e') => ",
                    "delta_step (red_def the_red_env) e e') ",
                    "(fun (h_step : delta_step (red_def the_red_env) e e') => h_step) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reverse bridge: every delta_reduces witness carries a genuine delta_step over the_red_env ",
                "(valid exactly because the family was tightened). Project the lone step field via ",
                "delta_reduces.rec. Part of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduces.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
