// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! App-case constructive sound theorem and dispatch wrapper (#461).
//!
//! `kernel_infer_app_sound` is the local bridge for the app case: given
//! infer-soundness for the strict subexpressions (f, a via IH), it
//! derives the spec `Typing.app` judgment by factoring through the WHNF
//! bridge on the inferred function type and the check bridge on the
//! argument.
//!
//! `infer_sound_at_app` is the KExpr.rec app-case handler for the
//! InferSoundAt motive, using the induction hypotheses to specialize
//! the IH parameters of kernel_infer_app_sound.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_app_sound(
        &mut self,
    ) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "kernel_infer_app_sound".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st (KExpr.app f a) -> ",
                "(forall (Tf : KExpr), KernelInferAccepts st f Tf -> has_type f Tf) -> ",
                "(forall (Ta : KExpr), KernelInferAccepts st a Ta -> has_type a Ta) -> ",
                "KernelInferAccepts st (KExpr.app f a) T -> ",
                "has_type (KExpr.app f a) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.app f a)) ",
                    "(hfun_sound : forall (Tf : KExpr), KernelInferAccepts st f Tf -> has_type f Tf) ",
                    "(harg_sound : forall (Ta : KExpr), KernelInferAccepts st a Ta -> has_type a Ta) ",
                    "(hinfer : KernelInferAccepts st (KExpr.app f a) T) => ",
                    // Eliminate the AppInferDecomp existential (binding the inferred
                    // subtypes Rf/Ra — KernelInferResult retired), then the
                    // AppInferWitness (binding the pi domain/codomain). Neither
                    // motive mentions the bound variables. The formerly-shared
                    // KernelInferResult st f is now the bound Rf (used by BOTH
                    // hfun_sound Rf hf and hwhnf over Rf); KernelInferResult st a is
                    // the bound Ra. No determinism, no Skolem.
                    "AppInferDecomp.rec st f a T ",
                    "(fun (_d : AppInferDecomp st f a T) => has_type (KExpr.app f a) T) ",
                    "(fun (Rf : KExpr) (Ra : KExpr) ",
                    "(hf : KernelInferAccepts st f Rf) ",
                    "(ha : KernelInferAccepts st a Ra) ",
                    "(hwit : AppInferWitness st Rf Ra a T) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st (KExpr.app f a) -> ",
                    "KernelInputAdmissible st Rf) => ",
                    "AppInferWitness.rec st Rf Ra a T ",
                    "(fun (_w : AppInferWitness st Rf Ra a T) => has_type (KExpr.app f a) T) ",
                    "(fun (dom : KExpr) (cod : KExpr) ",
                    "(hwhnf : KernelWhnfAccepts st Rf (KExpr.pi dom cod)) ",
                    "(hdefeq : KernelDefEqAccepts st Ra dom) ",
                    "(hresult : Eq KExpr (instantiate cod a) T) ",
                    "(hchkadm : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st a -> ",
                    "KernelBinaryInputAdmissible st Ra dom) => ",
                    "raw_type_conversion (KExpr.app f a) (instantiate cod a) T ",
                    "(Typing.app f a dom cod ",
                    "(raw_type_conversion f Rf (KExpr.pi dom cod) ",
                    "(hfun_sound Rf hf) ",
                    "(kernel_whnf_returns_def_eq st Rf (KExpr.pi dom cod) ",
                    "henv hctx ",
                    "(hguard henv hctx hadm) ",
                    "hwhnf)) ",
                    "(kernel_check_returns_well_typed_from_infer st a dom henv hctx ",
                    "(kernel_input_admissible_app_arg st f a hadm) ",
                    "harg_sound ",
                    "(KernelCheckAccepts.mk st a dom Ra ",
                    "(ProdType.mk (KernelInferAccepts st a Ra) ",
                    "(KernelDefEqAccepts st Ra dom) ",
                    "ha hdefeq) ",
                    "hchkadm))) ",
                    "(def_eq_eq_right (instantiate cod a) (instantiate cod a) T ",
                    "(DefEq.refl (instantiate cod a)) hresult)) ",
                    "hwit) ",
                    "(kernel_infer_app_decomposition st f a T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Constructive app-case infer_type local bridge: given infer-soundness for the strict subexpressions f and a, a successful app inference yields the spec Typing.app derivation. The proof eliminates the AppInferDecomp existential (binding the inferred subtypes Rf/Ra — KernelInferResult retired), then the AppInferWitness packaged existential (binding the pi domain/codomain), into the skolem-free has_type, factoring through the WHNF bridge on the inferred function type Rf and the local check_type bridge (KernelCheckAccepts built via KernelCheckAccepts.mk from the arg-infer acceptance at Ra and the witness def-eq/admissibility, sharing Ra by binding). Uses raw_type_conversion (raw bridge, Part of #2893). Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.app".to_string(),
                "raw_type_conversion".to_string(),
                "AppInferDecomp".to_string(),
                "AppInferDecomp.rec".to_string(),
                "AppInferWitness".to_string(),
                "AppInferWitness.rec".to_string(),
                "KernelCheckAccepts".to_string(),
                "KernelCheckAccepts.mk".to_string(),
                "ProdType.mk".to_string(),
                "kernel_whnf_returns_def_eq".to_string(),
                "kernel_check_returns_well_typed_from_infer".to_string(),
                "kernel_input_admissible_app_arg".to_string(),
                "kernel_infer_app_decomposition".to_string(),
                "def_eq_eq_right".to_string(),
                "DefEq.refl".to_string(),
            ])),
            // Eliminates AppInferDecomp + AppInferWitness (inferred subtypes and pi
            // domain/codomain bound internally — all Skolems retired); residual
            // closure is empty (all sub-lemmas are skolem-free after the reframe).
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Dispatch wrapper: infer_sound_at_app
        // =========================================================
        //
        // KExpr.rec app-case handler for InferSoundAt motive. This is the
        // only case that uses the KExpr.rec induction hypotheses: ihf/iha
        // provide InferSoundAt for the function/argument subexpressions.
        // The wrapper specializes them to the current kernel state and
        // supplies admissibility via constructive inversions.

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_app".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr), ",
                "InferSoundAt f -> InferSoundAt a -> ",
                "InferSoundAt (KExpr.app f a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) ",
                    "(ihf : InferSoundAt f) (iha : InferSoundAt a) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.app f a)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.app f a) T) => ",
                    "kernel_infer_app_sound st f a T henv hctx hadm ",
                    "(fun (Tf : KExpr) (haccf : KernelInferAccepts st f Tf) => ",
                    "ihf st Tf henv hctx ",
                    "(kernel_input_admissible_app_fun st f a hadm) haccf) ",
                    "(fun (Ta : KExpr) (hacca : KernelInferAccepts st a Ta) => ",
                    "iha st Ta henv hctx ",
                    "(kernel_input_admissible_app_arg st f a hadm) hacca) ",
                    "hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec app-case handler for the InferSoundAt motive. ",
                "Uses the induction hypotheses ihf/iha (InferSoundAt for the ",
                "function and argument subexpressions) together with ",
                "admissibility inversions to supply the IH parameters of ",
                "kernel_infer_app_sound. This is the only case that uses the ",
                "KExpr.rec induction hypotheses. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_app_sound".to_string(),
                "kernel_input_admissible_app_fun".to_string(),
                "kernel_input_admissible_app_arg".to_string(),
            ])),
            // kernel_infer_app_fun_step, kernel_infer_app_pi_step,
            // kernel_infer_app_arg_check_step, and kernel_infer_app_result_step
            // are now DerivedLemma projections, so we expand through to their
            // single HelperAxiom dep: kernel_infer_app_decomposition.
            // kernel_infer_app_decomposition and
            // kernel_infer_app_fun_type_admissible are no longer axiom leaves
            // (derived via kernel_infer_inversion); expand through to the master
            // inversion's residual closure (10 infer-band skolems +
            // KernelCheckAccepts) plus the check/defeq band.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_app_sound_tests.rs"]
mod implementation_soundness_infer_refinement_app_sound_tests;
