// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constructive lam/pi sound theorems and KExpr.rec dispatch wrappers (#461).
//!
//! Split from `implementation_soundness_infer_refinement_binder_typing.rs`
//! which provides the typing-level ProdType projections. This module assembles
//! those projections into constructive proof terms that promote
//! `kernel_infer_lam_sound` / `kernel_infer_pi_sound` from HelperAxiom to
//! DerivedPending, and provides the `infer_sound_at_lam` /
//! `infer_sound_at_pi` KExpr.rec dispatch wrappers.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_binder_sound(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Constructive lam/pi sound theorems (DerivedPending)
        // =========================================================

        self.add_definition(SpecDefinition {
            name: "kernel_infer_lam_sound".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st (KExpr.lam A body) -> ",
                "KernelInferAccepts st (KExpr.lam A body) T -> ",
                "has_type (KExpr.lam A body) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.lam A body)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lam A body) T) => ",
                    // Eliminate the LamInferDecomp existential (binding the inferred
                    // body type bt and the recursive body-infer premise), then the
                    // LamInferWitness (domain-sort / body-typing / result-eq): neither
                    // motive mentions the bound variables. The recursive body-infer
                    // premise hbody_infer is CARRIED but not consumed this stage — the
                    // body typing comes from the retained LamInferWitness `Typing body
                    // bt` field (the FVar-model-gap jump), since routing it through
                    // infer-soundness needs the lam body's binder-crossing
                    // admissibility (Stage 2 / infer_preserves_closed). Mirrors
                    // kernel_infer_app_sound's AppInferDecomp elimination.
                    "LamInferDecomp.rec st A body T ",
                    "(fun (_d : LamInferDecomp st A body T) => has_type (KExpr.lam A body) T) ",
                    "(fun (bt : KExpr) (hbody_infer : KernelInferAccepts st body bt) ",
                    "(hwit : LamInferWitness A body bt T) => ",
                    "LamInferWitness.rec A body bt T ",
                    "(fun (_w : LamInferWitness A body bt T) => has_type (KExpr.lam A body) T) ",
                    "(fun (dl : Level) ",
                    "(hdom : Typing A (KExpr.sort dl)) ",
                    "(hbody : Typing body bt) ",
                    "(hresult : Eq KExpr (KExpr.pi A bt) T) => ",
                    "raw_type_conversion (KExpr.lam A body) (KExpr.pi A bt) T ",
                    "(Typing.lam A body bt dl hdom hbody) ",
                    "(def_eq_eq_right (KExpr.pi A bt) (KExpr.pi A bt) T ",
                    "(DefEq.refl (KExpr.pi A bt)) hresult)) ",
                    "hwit) ",
                    "(kernel_infer_lam_decomposition st A body T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Constructive lam-case infer_type local bridge: a successful lam ",
                "inference yields the spec Typing.lam derivation by eliminating the ",
                "LamInferWitness packaged existential (binding the body type and domain ",
                "level internally — Skolems retired) into the skolem-free has_type. The ",
                "witness's domain-sort / body-typing / result-conversion fields drive ",
                "Typing.lam and raw_type_conversion. The universe bridge is resolved: ",
                "Typing.lam accepts Typing A (Sort u) for arbitrary u per #2870. Uses ",
                "raw_type_conversion (raw bridge, Part of #2893). Part of #2869, Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "raw_type_conversion".to_string(),
                "Typing.lam".to_string(),
                "LamInferDecomp".to_string(),
                "LamInferDecomp.rec".to_string(),
                "LamInferWitness".to_string(),
                "LamInferWitness.rec".to_string(),
                "kernel_infer_lam_decomposition".to_string(),
                "def_eq_eq_right".to_string(),
                "DefEq.refl".to_string(),
            ])),
            // Eliminates LamInferWitness (lam body-type/domain-level retired);
            // residual is the master inversion's single surviving skolem.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_infer_pi_sound".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (A : KExpr) (B : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st (KExpr.pi A B) -> ",
                "KernelInferAccepts st (KExpr.pi A B) T -> ",
                "has_type (KExpr.pi A B) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (A : KExpr) (B : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.pi A B)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.pi A B) T) => ",
                    // Eliminate PiInferWitness (packaged existential of the domain
                    // level dom and codomain level cod) into the skolem-free
                    // has_type: the motive does NOT mention dom/cod. The bound
                    // fields (hdom, hcod, hresult) pin dom/cod to A's/B's actual
                    // sort levels, so sort (imax_nat dom cod) is the genuine Pi
                    // type — not a free level.
                    "PiInferWitness.rec A B T ",
                    "(fun (_w : PiInferWitness A B T) => has_type (KExpr.pi A B) T) ",
                    "(fun (dom : Level) (cod : Level) ",
                    "(hdom : Typing A (KExpr.sort dom)) ",
                    "(hcod : Typing B (KExpr.sort cod)) ",
                    "(hresult : Eq KExpr (KExpr.sort (Level.imax dom cod)) T) => ",
                    "raw_type_conversion (KExpr.pi A B) (KExpr.sort (Level.imax dom cod)) T ",
                    "(Typing.pi A B dom cod hdom hcod) ",
                    "(def_eq_eq_right (KExpr.sort (Level.imax dom cod)) (KExpr.sort (Level.imax dom cod)) T ",
                    "(DefEq.refl (KExpr.sort (Level.imax dom cod))) hresult)) ",
                    "(kernel_infer_pi_decomposition st A B T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Constructive pi-case infer_type local bridge: a successful pi ",
                "inference yields the spec Typing.pi derivation by eliminating the ",
                "PiInferWitness packaged existential (binding the domain/codomain levels ",
                "internally — Skolems retired) into the skolem-free has_type. The ",
                "witness's domain-sort / codomain-sort / result-conversion fields drive ",
                "Typing.pi and raw_type_conversion; the typing fields pin the levels to ",
                "A's/B's actual sort levels. The universe bridge is resolved: Typing.pi ",
                "concludes Sort(imax_nat n m), matching the kernel's Sort(imax(l1, l2)) ",
                "per #2870. Uses raw_type_conversion (raw bridge, Part of #2893). ",
                "Part of #2869, Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "raw_type_conversion".to_string(),
                "Typing.pi".to_string(),
                "PiInferWitness".to_string(),
                "PiInferWitness.rec".to_string(),
                "imax_nat".to_string(),
                "kernel_infer_pi_decomposition".to_string(),
                "def_eq_eq_right".to_string(),
                "DefEq.refl".to_string(),
            ])),
            // Eliminates PiInferWitness (pi domain/codomain levels retired);
            // residual is the master inversion's single surviving skolem.
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Dispatch wrappers: infer_sound_at_lam, infer_sound_at_pi
        // =========================================================
        //
        // KExpr.rec case handlers for InferSoundAt motive. Both delegate
        // directly to the per-case sound theorems — the IH terms from
        // KExpr.rec are unused because subexpression typing is handled
        // by the binder-step axioms.

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_lam".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (body : KExpr), ",
                "InferSoundAt A -> InferSoundAt body -> ",
                "InferSoundAt (KExpr.lam A body)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (body : KExpr) ",
                    "(_ihA : InferSoundAt A) (_ihbody : InferSoundAt body) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.lam A body)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lam A body) T) => ",
                    "kernel_infer_lam_sound st A body T henv hctx hadm hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec lam-case handler for the InferSoundAt motive. ",
                "Delegates directly to kernel_infer_lam_sound. The IH terms ",
                "_ihA/_ihbody are unused because lam_sound's subexpression ",
                "typing is handled by binder-step axioms. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_lam_sound".to_string(),
            ])),
            // The consolidated decomposition parent is no longer an axiom leaf
            // (derived via kernel_infer_inversion); expand through to the master
            // inversion's residual closure: the single surviving skolem
            // KernelInferResult.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_pi".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr), ",
                "InferSoundAt A -> InferSoundAt B -> ",
                "InferSoundAt (KExpr.pi A B)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) ",
                    "(_ihA : InferSoundAt A) (_ihB : InferSoundAt B) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.pi A B)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.pi A B) T) => ",
                    "kernel_infer_pi_sound st A B T henv hctx hadm hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec pi-case handler for the InferSoundAt motive. ",
                "Delegates directly to kernel_infer_pi_sound. The IH terms ",
                "_ihA/_ihB are unused because pi_sound's subexpression ",
                "typing is handled by binder-step axioms. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_pi_sound".to_string(),
            ])),
            // The consolidated decomposition parent is no longer an axiom leaf
            // (derived via kernel_infer_inversion); expand through to the master
            // inversion's residual closure: the single surviving skolem
            // KernelInferResult.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_binder_typing_tests.rs"]
mod implementation_soundness_infer_refinement_binder_typing_tests;
