// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Binder-case infer_type refinement: cert-backed witness surface for lam/pi (#2869).
//!
//! The production kernel's lam/pi branches push a fresh local declaration,
//! open the binder body with an implementation FVar, recursively infer under
//! the extended local context, then close the result back over the binder via
//! `abstract_fvar` / the certificate rebind path.
//!
//! The core `KExpr` model has no FVar constructor and `KernelInputAdmissible`
//! reduces to `is_closed`. Rather than widening the expression model, this
//! module introduces cert-backed binder witnesses that describe the recursive
//! subcall *after* rebinding — staying inside the current closed `KExpr` model.
//!
//! The lam/pi decomposition lemmas recover the binder-step observations from
//! the faithful KernelInferAccepts inductive via kernel_infer_inversion. Each
//! now yields the Lam/PiInferWitness existential DIRECTLY: the vestigial
//! KernelLam/PiBodyAdmissible guards (and their dead-end ProdType.fst body-step
//! projections) were RETIRED (census 18->16). The constructive proof terms for
//! `kernel_infer_lam_sound` / `kernel_infer_pi_sound` are in the companion
//! module `implementation_soundness_infer_refinement_binder_typing`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_binder(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Binder-local witness definitions (Skolem witnesses)
        // =========================================================
        //
        // The former binder skolems (KernelLamBodyType, KernelLamDomainLevel,
        // KernelPiDomainLevel, KernelPiCodomainLevel) are retired into the
        // Lam/PiInferWitness existentials, and the two binder-admissibility
        // guards (KernelLamBodyAdmissible / KernelPiBodyAdmissible) are RETIRED
        // outright as vestigial (census 18->16). The only surviving infer-band
        // skolem is KernelInferResult, registered in
        // implementation_soundness_infer_accepts.rs (Step 3) BEFORE the faithful
        // KernelInferAccepts inductive.

        // =========================================================
        // Consolidated lam infer decomposition axiom
        // =========================================================
        //
        // Single structured axiom capturing the production lam branch:
        //   1. The binder-local recursive subcall is admissible (body step)
        //   2. The result is Pi(A, KernelLamBodyType) (result step)
        //   3. The domain A has a sort type (domain sort)
        //   4. The body has type KernelLamBodyType (body typing)
        //
        // All four observations are packaged as a nested ProdType 4-tuple.
        // This replaces what were previously four independent HelperAxioms
        // (kernel_infer_lam_body_step, kernel_infer_lam_result_step,
        // kernel_infer_lam_domain_sort, kernel_infer_lam_body_typing)
        // with one observation + four projections. Mirrors the
        // app_decomposition consolidation pattern.

        // kernel_infer_lam_decomposition: formerly a HelperAxiom, now DERIVED —
        // the lam constructor's single field IS this 4-tuple verbatim
        // (unguarded, exactly as the old axiom: deliberate exact-strength
        // preservation of the pre-existing FVar-model gap jump; see the ctor
        // comment in implementation_soundness_infer_accepts.rs), recovered by
        // the master inversion.
        self.add_definition(SpecDefinition {
            name: "kernel_infer_lam_decomposition".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr), ",
                "KernelInferAccepts st (KExpr.lam A body) T -> ",
                "LamInferDecomp st A body T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lam A body) T) => ",
                    "kernel_infer_inversion st (KExpr.lam A body) T hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Consolidated lam infer_type decomposition: a successful infer_type on ",
                "Lam(A, body) internally (1) admits the binder-local recursive subcall, ",
                "(2) returns a type definitionally equal to Pi(A, bodyType), ",
                "(3) ensures the domain A is a sort, and ",
                "(4) types the body under the pushed binder — all bound inside the ",
                "LamInferWitness existential. Directly reflects the production ",
                "implementation in clean-kernel/src/tc/infer.rs. DERIVED from the faithful ",
                "KernelInferAccepts inductive via kernel_infer_inversion (the lam ",
                "constructor now carries exactly this witness; the vestigial ",
                "KernelLamBodyAdmissible guard was retired). Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts".to_string(),
                "LamInferDecomp".to_string(),
                "LamInferWitness".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
            ])),
            // Residual closure through the master inversion: the single surviving
            // skolem KernelInferResult; the lam body-type/domain-level Skolems are
            // retired into LamInferWitness (debt golden tracks this).
            axiom_deps: HashSet::new(),
        })?;

        // kernel_infer_lam_body_step is RETIRED (census 18->16): it was a
        // dead-end ProdType.fst projection of the vestigial KernelLamBodyAdmissible
        // guard (consumed by nothing but tests + the ProofLibrary twin). With the
        // guard dropped from the lam ctor field there is nothing to project.

        // kernel_infer_lam_result_step (is_def_eq (Pi A bodyType) T) is RETIRED:
        // its type named the KernelLamBodyType Skolem, now bound internally by
        // LamInferWitness. The lam result-conversion is recovered directly inside
        // kernel_infer_lam_sound's LamInferWitness.rec elimination.

        // =========================================================
        // Consolidated pi infer decomposition axiom
        // =========================================================
        //
        // Single structured axiom capturing the production pi branch:
        //   1. The binder-local recursive subcall is admissible (body step)
        //   2. The domain A has a sort type (domain sort)
        //   3. The codomain B has a sort type (codomain sort)
        //   4. The result equals Sort(imax_nat(dom, cod)) (imax result step)
        //
        // All four observations are packaged as a nested ProdType 4-tuple. The
        // redundant Sort(KernelPiBodyLevel) result-step conjunct was retired —
        // the imax conjunct is the faithful pi-typing rule and pinned T
        // identically, so KernelPiBodyLevel carried no independent content.

        // kernel_infer_pi_decomposition: formerly a HelperAxiom, now DERIVED —
        // the pi constructor's single field IS this 4-tuple verbatim (unguarded,
        // exactly as the old axiom: deliberate exact-strength preservation; see
        // the ctor comment in implementation_soundness_infer_accepts.rs),
        // recovered by the master inversion.
        self.add_definition(SpecDefinition {
            name: "kernel_infer_pi_decomposition".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (A : KExpr) (B : KExpr) (T : KExpr), ",
                "KernelInferAccepts st (KExpr.pi A B) T -> ",
                "PiInferWitness A B T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (A : KExpr) (B : KExpr) (T : KExpr) ",
                    "(hinfer : KernelInferAccepts st (KExpr.pi A B) T) => ",
                    "kernel_infer_inversion st (KExpr.pi A B) T hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Consolidated pi infer_type decomposition: a successful infer_type on ",
                "Pi(A, B) internally (1) admits the binder-local recursive subcall, and ",
                "(2) satisfies the PiInferWitness (domain A is a sort at some level dom, ",
                "codomain B is a sort at some level cod, and the result is definitionally ",
                "equal to Sort(imax_nat(dom, cod))). DERIVED from the faithful ",
                "KernelInferAccepts inductive via kernel_infer_inversion (the pi ",
                "constructor now carries exactly this witness DIRECTLY; the vestigial ",
                "KernelPiBodyAdmissible guard was retired). The domain/codomain levels are ",
                "bound INTERNALLY by PiInferWitness (Skolems retired). Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts".to_string(),
                "PiInferWitness".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
            ])),
            // Residual closure through the master inversion: the single surviving
            // skolem KernelInferResult; the pi domain/codomain level Skolems are
            // retired into PiInferWitness (debt golden tracks this).
            axiom_deps: HashSet::new(),
        })?;

        // kernel_infer_pi_body_step is RETIRED (census 18->16): it was a dead-end
        // ProdType.fst projection of the vestigial KernelPiBodyAdmissible guard
        // (consumed by nothing but tests + the ProofLibrary twin). With the guard
        // dropped from the pi ctor field there is nothing to project.

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_binder_tests.rs"]
mod implementation_soundness_infer_refinement_binder_tests;
