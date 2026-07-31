// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! App-case infer_type local bridge over the later decomposition modules (#461).
//!
//! The production kernel's app branch:
//! 1. infers the function type,
//! 2. WHNFs that type to a Pi domain/codomain pair,
//! 3. checks the argument against the Pi domain, and
//! 4. returns the instantiated codomain.
//!
//! Unlike the sort/bvar cases, the constructive proof here needs the later
//! WHNF/check decomposition theorems. This module is therefore registered after
//! `implementation_soundness_whnf_decomposition.rs`,
//! `implementation_soundness_defeq_decomposition.rs`, and
//! `implementation_soundness_check_decomposition.rs`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_app(
        &mut self,
    ) -> Result<(), SpecError> {
        // KernelInferAppPiDomain / KernelInferAppPiCodomain are now registered
        // in implementation_soundness_infer_accepts.rs (PART 21, Step 3), BEFORE
        // the faithful KernelInferAccepts inductive whose app constructor's
        // fields bind at the skolem applications. They remain opaque
        // HelperAxioms there — residual named trust content of the infer model.

        // =========================================================
        // Consolidated app infer decomposition (formerly a HelperAxiom)
        // =========================================================
        //
        // Single structured observation that a successful infer_type on (f a)
        //   1. infers the function subexpression f,
        //   2. WHNFs the inferred type to a Pi domain/codomain pair,
        //   3. checks the argument against the Pi domain, and
        //   4. returns the instantiated codomain,
        // packaged as a nested ProdType 4-tuple. With KernelInferAccepts a
        // faithful inductive, this is now DERIVED: the app constructor carries
        // the recursive premise (field 1) and the whnf/check/result tuple
        // (field 2) — exactly this 4-tuple, split only to keep the recursive
        // occurrence strictly positive — and the master inversion repackages
        // them (ProdType.mk) so this projection is byte-identical to the old
        // axiom. Unguarded, exactly as the old axiom was.

        self.add_definition(SpecDefinition {
            name: "kernel_infer_app_decomposition".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr), ",
                "KernelInferAccepts st (KExpr.app f a) T -> ",
                "AppInferDecomp st f a T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr) ",
                    "(hinfer : KernelInferAccepts st (KExpr.app f a) T) => ",
                    "kernel_infer_inversion st (KExpr.app f a) T hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Consolidated app infer_type decomposition: a successful infer_type on ",
                "(f a) internally (1) infers f yielding some type Rf, ",
                "(2) infers the argument a yielding some type Ra, ",
                "(3) satisfies the AppInferWitness (WHNFs Rf to a Pi ",
                "domain/codomain pair, def-eq-checks Ra against that ",
                "domain, and returns a type definitionally equal to the instantiated codomain), ",
                "and (4) Rf is admissible — all packaged in the AppInferDecomp existential, which ",
                "binds Rf/Ra INTERNALLY (the un-Skolemization retiring KernelInferResult). ",
                "Directly reflects the production implementation in clean-kernel/src/tc/infer.rs. ",
                "DERIVED from the faithful KernelInferAccepts inductive via kernel_infer_inversion ",
                "(the app payload IS AppInferDecomp by iota-reduction; unguarded exactly as the old ",
                "axiom was). The pi domain/codomain are bound INTERNALLY by AppInferWitness and the ",
                "inferred subtypes by AppInferDecomp (Skolems retired). Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts".to_string(),
                "AppInferDecomp".to_string(),
                "AppInferWitness".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
            ])),
            // Existential decomposition via the master inversion: no surviving skolem —
            // the inferred subtypes Rf/Ra are bound internally by AppInferDecomp and the
            // pi domain/codomain by AppInferWitness (kernel-generated inductives).
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Derived step projections — RETIRED (un-Skolemization)
        // =========================================================
        //
        // kernel_infer_app_fun_step and kernel_infer_app_fun_type_admissible were
        // RETIRED by the KernelInferResult un-Skolemization: their types named the
        // inferred function type as the Skolem KernelInferResult st f, which no
        // longer exists (the inferred subtypes Rf/Ra are now existentially bound
        // inside AppInferDecomp / the app constructor). A standalone projection to
        // `KernelInferAccepts st f Rf` for an existentially-bound Rf loses the
        // R-sharing that made it useful and is not expressible as a named lemma
        // type — exactly the reason the def-eq band retired KernelDefEqNormalLeft/
        // Right rather than projecting them. The fun-infer acceptance, the fun-type
        // admissibility guard, and the WHNF/check/result evidence are all recovered
        // directly inside kernel_infer_app_sound by eliminating AppInferDecomp (bind
        // Rf/Ra) and then AppInferWitness (bind dom/cod). This is the same
        // retirement the app whnf/arg-check/result step projections already
        // received when the pi domain/codomain Skolems were bound inside
        // AppInferWitness.
        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_app_tests.rs"]
mod implementation_soundness_infer_refinement_app_tests;
