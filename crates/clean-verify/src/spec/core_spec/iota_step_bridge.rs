// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment D (#2859 computational-iota/delta track): bridge the computational
//! `iota_step` to the abstract `iota_reduces` family — drop-in, path D(i).
//!
//! `iota_reduces.mk` requires the reduct to be DefEq to the redex (`h_subst`) and
//! type-preserving (`h_fwd`/`h_bwd`). With the opaque `RecRule.rhs`, those facts
//! are NOT derivable from `iota_step` alone — they hold only when each rule's
//! `rhs` genuinely computes a faithful reduct. That guarantee is the
//! `RecEnvWellformed` predicate (a real inductive carrying the three
//! universally-quantified faithfulness facts — the analogue of the existing
//! `WellFormedCtorDecls` interface, `env_extensions.rs:87`). It is NOT an axiom:
//! it is a *defined* hypothesis whose witness, for the kernel's actual recursor
//! environment, is discharged constructively at the end of the track by modeling
//! `build_recursor_rule_rhs`. So this REPLACES the false `church_rosser_whnf`
//! with a true faithful-interface predicate — net trust strictly improves.
//!
//! `iota_step_to_reduces` projects the three facts and applies `iota_reduces.mk`,
//! so the whole existing `iota_reduces` surface (the 4 `iota` constructors, the
//! recursor, the 3 transport lemmas) is preserved unchanged (path D(i)).
//! See `designs/2026-06-14-computational-iota-delta-track.md` (Increment D).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The DefEq-faithfulness fact carried by `RecEnvWellformed env`.
const WF_SUBST: &str = "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
/// The forward type-preservation fact.
const WF_FWD: &str = "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
/// The backward type-preservation fact.
const WF_BWD: &str = "forall (e : KExpr) (e' : KExpr), iota_step env e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

impl Specification {
    pub(super) fn add_iota_step_bridge(&mut self) -> Result<(), SpecError> {
        // RecEnvWellformed env: the faithful-interface predicate. A real
        // inductive (proper recursor, not an axiom projector) carrying the three
        // facts iota_reduces.mk needs, universally over the env's iota steps.
        self.add_inductive(
            &format!(
                "inductive RecEnvWellformed (env : RecEnv) : Type\n| mk : ({WF_SUBST}) → ({WF_FWD}) → ({WF_BWD}) → RecEnvWellformed env"
            ),
            "Faithfulness interface for a recursor environment: every computational iota_step \
             yields a DefEq-to-redex (h_subst) and bidirectional typing transfer (h_fwd/h_bwd). \
             A defined hypothesis (NOT an axiom); its witness for the kernel env is discharged \
             at the end of the track. Part of #2859 (Increment D).",
        )?;

        // iota_step_to_reduces: the FORWARD bridge, simplified for the tightened
        // family. The family ctor now carries the step itself, so the bridge just
        // wraps it (no RecEnvWellformed projection — the three faithfulness facts
        // moved to the transport lemmas, which project them from RecEnvWellformed).
        // Env pinned to the fixed the_red_env (NOT forall env).
        self.add_definition(SpecDefinition {
            name: "iota_step_to_reduces".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "iota_step (red_rec the_red_env) e e' -> iota_reduces e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(h : iota_step (red_rec the_red_env) e e') => ",
                    "iota_reduces.mk e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Forward bridge: a computational iota_step over the fixed the_red_env yields an ",
                "abstract iota_reduces witness (just apply the tightened iota_reduces.mk to the step). ",
                "Env pinned to the_red_env. DerivedProved; the only axiom dep is iota_reduces itself ",
                "(it constructs one). Part of the church_rosser_whnf retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduces.mk".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::from(["iota_reduces".to_string()]),
        })?;

        // iota_reduces_to_step: the REVERSE bridge — now VALID because the tightened
        // family's sole inhabitant IS a step (it was FALSE for the loose family, whose
        // refl witnesses carried no step). Project the lone field via iota_reduces.rec.
        // Since iota_reduces is now a GENUINE inductive (Bricks R0+R1), iota_reduces.rec
        // is the KERNEL-GENERATED recursor in the PROMOTED-PARAMETER (AndType) shape: the
        // e/e' indices are IMPLICIT params, the motive ranges over the major premise only,
        // and the single minor has no index binders — so the recursor takes just
        // (motive, minor, major) with e/e' inferred (NOT the retired hand-axiom's 3-ary
        // index-motive shape). A total function, NOT ex-falso. The engine of
        // def_eq_joinable's iota arm.
        self.add_definition(SpecDefinition {
            name: "iota_reduces_to_step".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "iota_reduces e e' -> iota_step (red_rec the_red_env) e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : iota_reduces e e') => ",
                    "iota_reduces.rec ",
                    "(fun (_ : iota_reduces e e') => ",
                    "iota_step (red_rec the_red_env) e e') ",
                    "(fun (h_step : iota_step (red_rec the_red_env) e e') => h_step) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reverse bridge: every iota_reduces witness carries a genuine iota_step over the_red_env ",
                "(valid exactly because the family was tightened — false for the old loose family). ",
                "Project the lone step field via iota_reduces.rec. Part of the church_rosser_whnf ",
                "retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduces.rec".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
