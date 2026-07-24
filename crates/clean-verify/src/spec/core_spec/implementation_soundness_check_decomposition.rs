// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! check_type decomposition: infer_type + is_def_eq (#461).
//!
//! Split from implementation_soundness.rs. Contains:
//! - kernel_check_decomposition: the structured decomposition (infer + defeq
//!   steps), DERIVED via KernelCheckAccepts.rec since Step 4
//! - kernel_check_infer_step, kernel_check_defeq_step: DerivedLemma projections
//! - kernel_check_types_admissible: admissibility transfer, DERIVED via
//!   KernelCheckAccepts.rec since Step 4
//! - kernel_check_returns_well_typed_from_infer: local bridge using an infer-soundness premise
//! - kernel_check_returns_well_typed: DerivedLemma with constructive proof term
//!   registered after the infer dispatch wrappers so it can reuse the global
//!   infer theorem
//!
//! The production kernel's check_type is implemented as:
//!   let inferred = infer_type(e)?;
//!   if !is_def_eq(&inferred, expected) { return Err(...); }
//!
//! This module decomposes KernelCheckAccepts into its constituent steps.
//! KernelCheckAccepts is no longer an opaque axiom: it is a faithful
//! single-constructor inductive (implementation_soundness_infer_accepts.rs,
//! Step 4) whose mk constructor carries exactly (1) the unguarded infer+defeq
//! ProdType pair and (2) the guarded admissibility implication — so both
//! formerly-assumed axioms here are now DERIVED by KernelCheckAccepts.rec, no
//! longer assumed. The local bridge is registered early so infer/app proofs
//! can use it without recursion through the global infer theorem; the global
//! check theorem is registered later once the constructive infer dispatch is
//! available.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_check_decomposition(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Deterministic result functions (Skolem witnesses)
        // =========================================================
        //
        // KernelInferResult is now registered in
        // implementation_soundness_infer_accepts.rs (PART 21, Step 3), BEFORE
        // the faithful KernelInferAccepts inductive whose app constructor's
        // recursive field binds at the skolem application. It remains an opaque
        // HelperAxiom there — residual named trust content of the infer model.

        // =========================================================
        // check_type decomposition/step projections — RETIRED (un-Skolemization)
        // =========================================================
        //
        // kernel_check_decomposition, kernel_check_infer_step,
        // kernel_check_defeq_step, and kernel_check_types_admissible were RETIRED
        // by the KernelInferResult un-Skolemization: every one of their types named
        // the inferred type as the Skolem KernelInferResult st e, which no longer
        // exists (KernelCheckAccepts.mk now binds the inferred type R EXISTENTIALLY,
        // shared by binding between the infer and defeq halves). A standalone
        // projection to `KernelInferAccepts st e R` / `KernelDefEqAccepts st R T` for
        // an existentially-bound R loses the R-sharing that made the pair coherent
        // and is not expressible as a named lemma type — exactly why the def-eq band
        // retired KernelDefEqNormalLeft/Right rather than projecting them. The infer
        // half, the defeq half, and the admissibility guard are now recovered
        // directly by eliminating KernelCheckAccepts.rec (binding R) inside
        // kernel_check_returns_well_typed_from_infer (soundness) and
        // tc_check_completeness (the CheckDecomp existential). The exact-strength
        // content the old axioms carried is preserved by KernelCheckAccepts.mk's two
        // fields — verified by the recursor-shape tests.

        // =========================================================
        // Derived: kernel_check_returns_well_typed_from_infer
        // =========================================================
        //
        // Local bridge: if the caller can already translate infer_type success
        // on e to has_type e _, then check_type soundness follows without
        // referencing the global kernel_infer_returns_well_typed theorem.
        //
        // This is the shape needed inside infer_type case proofs, where KExpr.rec
        // provides infer-soundness only for strict subexpressions.

        self.add_definition(SpecDefinition {
            name: "kernel_check_returns_well_typed_from_infer".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st e -> ",
                "(forall (T' : KExpr), KernelInferAccepts st e T' -> has_type e T') -> ",
                "KernelCheckAccepts st e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer_sound : forall (T' : KExpr), KernelInferAccepts st e T' -> has_type e T') ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    // Eliminate KernelCheckAccepts.rec, binding the inferred type R
                    // (KernelInferResult retired). The two halves of the ProdType pair
                    // reference the SAME bound R (shared by binding, not by a Skolem):
                    // the infer half feeds hinfer_sound, the defeq half + guard feed
                    // kernel_def_eq_reflects_spec, and raw_type_conversion joins them.
                    "KernelCheckAccepts.rec st e T ",
                    "(fun (_c : KernelCheckAccepts st e T) => has_type e T) ",
                    "(fun (R : KExpr) ",
                    "(hpair : ProdType (KernelInferAccepts st e R) (KernelDefEqAccepts st R T)) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st e -> KernelBinaryInputAdmissible st R T) => ",
                    "raw_type_conversion e R T ",
                    "(hinfer_sound R ",
                    "(ProdType.fst (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) hpair)) ",
                    "(kernel_def_eq_reflects_spec st R T ",
                    "henv hctx ",
                    "(hguard henv hctx hadm) ",
                    "(ProdType.snd (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) hpair))) ",
                    "hcheck"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Local check_type soundness bridge parameterized by infer-soundness on the same expression. This avoids a recursive dependency on the global infer theorem inside infer_type case proofs while still mirroring check_type = infer_type + is_def_eq. Proved by eliminating KernelCheckAccepts.rec directly (binding the inferred type R — KernelInferResult retired; the infer and defeq halves share R by binding), then raw_type_conversion over the infer-soundness premise and kernel_def_eq_reflects_spec. Uses raw_type_conversion (raw bridge, Part of #2893). Part of #461."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "raw_type_conversion".to_string(),
                "kernel_def_eq_reflects_spec".to_string(),
                "KernelCheckAccepts".to_string(),
                "KernelCheckAccepts.rec".to_string(),
                "KernelInferAccepts".to_string(),
                "KernelDefEqAccepts".to_string(),
                "ProdType.fst".to_string(),
                "ProdType.snd".to_string(),
                "has_type".to_string(),
            ])),
            // Eliminates KernelCheckAccepts.rec directly (inferred type R bound
            // existentially — KernelInferResult retired). kernel_def_eq_reflects_spec
            // is skolem-free (DefEqJoinable), so the residual closure is empty.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    pub(super) fn add_implementation_soundness_check_sound(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Derived: kernel_check_returns_well_typed
        // =========================================================
        //
        // Registered after the constructive infer dispatcher so the proof term
        // can reuse kernel_infer_returns_well_typed directly.

        self.add_definition(SpecDefinition {
            name: "kernel_check_returns_well_typed".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelCheckAccepts st e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    "kernel_check_returns_well_typed_from_infer st e T ",
                    "henv hctx hadm ",
                    "(fun (T' : KExpr) (hinfer : KernelInferAccepts st e T') => ",
                    "kernel_infer_returns_well_typed st e T' henv hctx hadm hinfer) ",
                    "hcheck"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Forward simulation for check_type: derived from decomposition. \
                          Proof: infer_type yields has_type e T', is_def_eq yields T' ≡ T, \
                          raw_type_conversion yields has_type e T. Mirrors the production \
                          implementation: check_type = infer_type + is_def_eq. \
                          Uses raw bridge (Part of #2893)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_check_returns_well_typed_from_infer".to_string(),
                "kernel_infer_returns_well_typed".to_string(),
                "KernelInferAccepts".to_string(),
                "has_type".to_string(),
            ])),
            // The check band is skolem-free after the KernelInferResult
            // un-Skolemization: kernel_check_returns_well_typed_from_infer
            // eliminates KernelCheckAccepts.rec directly (binding R),
            // kernel_def_eq_reflects_spec concludes in the non-axiom DefEqJoinable.
            // The named kernel_infer_returns_well_typed pending leaf stays surfaced
            // for the summary-layer audits.
            axiom_deps: HashSet::from(["kernel_infer_returns_well_typed".to_string()]),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_check_decomposition_tests.rs"]
mod implementation_soundness_check_decomposition_tests;
