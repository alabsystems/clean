// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Reduction witness transport lemmas (Part of #725, #464; church_rosser_whnf
//! retirement track).
//!
//! The six transport lemmas (subst-DefEq + bidirectional type-preservation for
//! delta/iota reductions). After the families were TIGHTENED to carry only an
//! operational step over the fixed `the_red_env`, the loose 3-field bundle the old
//! proofs projected is gone. Each lemma now takes the faithful-env interface as a
//! CARRIED HYPOTHESIS (`DefEnvWellformed the_red_env` / `RecEnvWellformed
//! (red_rec the_red_env)`), reverse-bridges the witness to its genuine step, and
//! projects the relevant single-step faithfulness fact (WF_SUBST / WF_FWD / WF_BWD)
//! from the interface via its recursor.
//!
//! GUARDS: the WF interface is a CARRIED hypothesis (Guard 3 — never axiomatized,
//! discharged at end-of-track by modeling the kernel env), the env is the literal
//! `the_red_env` (Guard 1 — no forall/exists env). Single-step subject reduction +
//! subst-DefEq, strictly weaker than confluence, NOT a join claim.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// The three δ faithfulness facts carried by `DefEnvWellformed the_red_env` (the
// `delta_step_bridge.rs` DEF_WF_* constants with env := the_red_env). Used as the
// explicit binder annotations of the DefEnvWellformed.rec minor premise.
const DEF_WF_SUBST_TRE: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def the_red_env) e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
const DEF_WF_FWD_TRE: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def the_red_env) e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
const DEF_WF_BWD_TRE: &str = "forall (e : KExpr) (e' : KExpr), delta_step (red_def the_red_env) e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

// The three ι faithfulness facts carried by `RecEnvWellformed (red_rec the_red_env)`
// (the `iota_step_bridge.rs` WF_* constants with env := red_rec the_red_env).
const REC_WF_SUBST_TRE: &str = "forall (e : KExpr) (e' : KExpr), iota_step (red_rec the_red_env) e e' -> forall (val : KExpr) (depth : Nat), DefEq (instantiate_at e val depth) (instantiate_at e' val depth)";
const REC_WF_FWD_TRE: &str = "forall (e : KExpr) (e' : KExpr), iota_step (red_rec the_red_env) e e' -> forall (T : KExpr), Typing e T -> Typing e' T";
const REC_WF_BWD_TRE: &str = "forall (e : KExpr) (e' : KExpr), iota_step (red_rec the_red_env) e e' -> forall (T : KExpr), Typing e' T -> Typing e T";

impl Specification {
    pub(super) fn add_reduction_witnesses(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Delta transport lemmas (carry DefEnvWellformed the_red_env)
        // =========================================================

        // delta_subst_preserves_def_eq_at: project WF_SUBST from DefEnvWellformed,
        // apply to the reverse-bridged step.
        self.add_definition(SpecDefinition {
            name: "delta_subst_preserves_def_eq_at".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr) (val : KExpr) (depth : Nat), ",
                "DefEnvWellformed the_red_env -> ",
                "delta_reduces e e' -> ",
                "DefEq (instantiate_at e val depth) (instantiate_at e' val depth)"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (val : KExpr) (depth : Nat) ",
                    "(w : DefEnvWellformed the_red_env) (h : delta_reduces e e') => ",
                    "DefEnvWellformed.rec the_red_env ",
                    "(fun (_ : DefEnvWellformed the_red_env) => ",
                    "DefEq (instantiate_at e val depth) (instantiate_at e' val depth)) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hs e e' (delta_reduces_to_step e e' h) val depth) ",
                    "w"
                ),
                SUBST = DEF_WF_SUBST_TRE,
                FWD = DEF_WF_FWD_TRE,
                BWD = DEF_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Delta subst-DefEq for a single step, from carried DefEnvWellformed the_red_env. Reverse-bridge + WF_SUBST projection. Part of #725, #464 (church_rosser_whnf retirement).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEnvWellformed.rec".to_string(),
                "delta_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_type_preservation_fwd: project WF_FWD.
        self.add_definition(SpecDefinition {
            name: "delta_type_preservation_fwd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "DefEnvWellformed the_red_env -> ",
                "delta_reduces e e' -> ",
                "forall (T : KExpr), has_type e T -> has_type e' T"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(w : DefEnvWellformed the_red_env) (h : delta_reduces e e') => ",
                    "DefEnvWellformed.rec the_red_env ",
                    "(fun (_ : DefEnvWellformed the_red_env) => ",
                    "forall (T : KExpr), has_type e T -> has_type e' T) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hf e e' (delta_reduces_to_step e e' h)) ",
                    "w"
                ),
                SUBST = DEF_WF_SUBST_TRE,
                FWD = DEF_WF_FWD_TRE,
                BWD = DEF_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Delta type preservation (forward) for a single step, from carried DefEnvWellformed. Part of #725, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEnvWellformed.rec".to_string(),
                "delta_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_type_preservation_bwd: project WF_BWD.
        self.add_definition(SpecDefinition {
            name: "delta_type_preservation_bwd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "DefEnvWellformed the_red_env -> ",
                "delta_reduces e e' -> ",
                "forall (T : KExpr), has_type e' T -> has_type e T"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(w : DefEnvWellformed the_red_env) (h : delta_reduces e e') => ",
                    "DefEnvWellformed.rec the_red_env ",
                    "(fun (_ : DefEnvWellformed the_red_env) => ",
                    "forall (T : KExpr), has_type e' T -> has_type e T) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hb e e' (delta_reduces_to_step e e' h)) ",
                    "w"
                ),
                SUBST = DEF_WF_SUBST_TRE,
                FWD = DEF_WF_FWD_TRE,
                BWD = DEF_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Delta type preservation (backward) for a single step, from carried DefEnvWellformed. Part of #725, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEnvWellformed.rec".to_string(),
                "delta_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Iota transport lemmas (carry RecEnvWellformed (red_rec the_red_env))
        // =========================================================

        // iota_subst_preserves_def_eq_at: project WF_SUBST from RecEnvWellformed.
        self.add_definition(SpecDefinition {
            name: "iota_subst_preserves_def_eq_at".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr) (val : KExpr) (depth : Nat), ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "iota_reduces e e' -> ",
                "DefEq (instantiate_at e val depth) (instantiate_at e' val depth)"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (val : KExpr) (depth : Nat) ",
                    "(w : RecEnvWellformed (red_rec the_red_env)) (h : iota_reduces e e') => ",
                    "RecEnvWellformed.rec (red_rec the_red_env) ",
                    "(fun (_ : RecEnvWellformed (red_rec the_red_env)) => ",
                    "DefEq (instantiate_at e val depth) (instantiate_at e' val depth)) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hs e e' (iota_reduces_to_step e e' h) val depth) ",
                    "w"
                ),
                SUBST = REC_WF_SUBST_TRE,
                FWD = REC_WF_FWD_TRE,
                BWD = REC_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Iota subst-DefEq for a single step, from carried RecEnvWellformed (red_rec the_red_env). Part of #725, #464 (church_rosser_whnf retirement).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvWellformed.rec".to_string(),
                "iota_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_type_preservation_fwd: project WF_FWD.
        self.add_definition(SpecDefinition {
            name: "iota_type_preservation_fwd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "iota_reduces e e' -> ",
                "forall (T : KExpr), has_type e T -> has_type e' T"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(w : RecEnvWellformed (red_rec the_red_env)) (h : iota_reduces e e') => ",
                    "RecEnvWellformed.rec (red_rec the_red_env) ",
                    "(fun (_ : RecEnvWellformed (red_rec the_red_env)) => ",
                    "forall (T : KExpr), has_type e T -> has_type e' T) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hf e e' (iota_reduces_to_step e e' h)) ",
                    "w"
                ),
                SUBST = REC_WF_SUBST_TRE,
                FWD = REC_WF_FWD_TRE,
                BWD = REC_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Iota type preservation (forward) for a single step, from carried RecEnvWellformed. Part of #725, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvWellformed.rec".to_string(),
                "iota_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_type_preservation_bwd: project WF_BWD.
        self.add_definition(SpecDefinition {
            name: "iota_type_preservation_bwd".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "iota_reduces e e' -> ",
                "forall (T : KExpr), has_type e' T -> has_type e T"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) ",
                    "(w : RecEnvWellformed (red_rec the_red_env)) (h : iota_reduces e e') => ",
                    "RecEnvWellformed.rec (red_rec the_red_env) ",
                    "(fun (_ : RecEnvWellformed (red_rec the_red_env)) => ",
                    "forall (T : KExpr), has_type e' T -> has_type e T) ",
                    "(fun (hs : {SUBST}) (hf : {FWD}) (hb : {BWD}) => ",
                    "hb e e' (iota_reduces_to_step e e' h)) ",
                    "w"
                ),
                SUBST = REC_WF_SUBST_TRE,
                FWD = REC_WF_FWD_TRE,
                BWD = REC_WF_BWD_TRE,
            )),
            is_axiom: false,
            description: "Iota type preservation (backward) for a single step, from carried RecEnvWellformed. Part of #725, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvWellformed.rec".to_string(),
                "iota_reduces_to_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
