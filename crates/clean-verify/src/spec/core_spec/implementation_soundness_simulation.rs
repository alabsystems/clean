// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Forward-simulation theorems and summary-alias wrappers for #461.
//!
//! Split from implementation_soundness.rs. Contains:
//! - Named forward-simulation theorems (KernelInferSound, KernelCheckSound, etc.)
//! - Summary-alias forward-simulation wrappers (*_summary variants)
//! - The KernelWhnfPreservesTyping derived corollary
//!
//! All definitions here depend on the state bridge and raw forward contracts
//! registered in `implementation_soundness.rs`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_simulation(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Named forward-simulation theorems (split-predicate interface)
        // =========================================================

        self.add_definition(SpecDefinition {
            name: "KernelInferSound".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (T : KExpr), KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st e -> KernelInferAccepts st e T -> has_type e T".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (T : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelInferAccepts st e T) => kernel_infer_returns_well_typed st e T henv hctx hin haccept".to_string()),
            is_axiom: false,
            description: "Named forward-simulation theorem for infer_type over the core specification fragment.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_infer_returns_well_typed".to_string(),
            ])),
            // The six per-case infer axioms are no longer axiom leaves (all
            // derived from the faithful KernelInferAccepts inductive via
            // kernel_infer_inversion); the remaining leaves are the master
            // inversion's residual closure (10 infer-band skolems +
            // KernelCheckAccepts) plus the check/defeq band.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelCheckSound".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (T : KExpr), KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st e -> KernelCheckAccepts st e T -> has_type e T".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (T : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelCheckAccepts st e T) => kernel_check_returns_well_typed st e T henv hctx hin haccept".to_string()),
            is_axiom: false,
            description: "Named forward-simulation theorem for check_type over the core specification fragment.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_check_returns_well_typed".to_string(),
            ])),
            // All DerivedLemma deps expanded to HelperAxiom deps:
            // kernel_def_eq_reflects_spec → Skolem witnesses;
            // kernel_check_infer_step/defeq_step → kernel_check_decomposition
            // → (Step 4) the faithful KernelCheckAccepts inductive's
            // skolem-witness closure.
            axiom_deps: HashSet::from([
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelWhnfSound".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (e' : KExpr), KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st e -> KernelWhnfAccepts st e e' -> is_def_eq e e'".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (e' : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') => kernel_whnf_returns_def_eq st e e' henv hctx hin haccept".to_string()),
            is_axiom: false,
            description: "Named forward-simulation theorem for whnf over the core specification fragment.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_whnf_returns_def_eq".to_string(),
            ])),
            // kernel_whnf_returns_def_eq now has an empty axiom closure (its
            // whnf bridge kernel_whnf_reduces_to_spec_whnf is a proved theorem,
            // not an axiom), so this forward-simulation wrapper inherits no
            // axiom leaves.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelDefEqSound".to_string(),
            type_src: "forall (st : KernelState) (a : KExpr) (b : KExpr), KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelBinaryInputAdmissible st a b -> KernelDefEqAccepts st a b -> is_def_eq a b".to_string(),
            value_src: Some("fun (st : KernelState) (a : KExpr) (b : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelBinaryInputAdmissible st a b) (haccept : KernelDefEqAccepts st a b) => kernel_def_eq_reflects_spec st a b henv hctx hin haccept".to_string()),
            is_axiom: false,
            description: "Named forward-simulation theorem for is_def_eq over the core specification fragment.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_def_eq_reflects_spec".to_string(),
            ])),
            // kernel_def_eq_reflects_spec is now skolem-free (KernelDefEqAccepts.mk
            // concludes in the non-axiom DefEqJoinable existential), so no residual leaf.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelWhnfPreservesTyping".to_string(),
            type_src: "forall (hf : RedEnvFaithful the_red_env) (st : KernelState) (e : KExpr) (e' : KExpr) (T : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelInputAdmissible st e -> KernelWhnfAccepts st e e' -> has_type e T -> has_type e' T".to_string(),
            value_src: Some("fun (hf : RedEnvFaithful the_red_env) (st : KernelState) (e : KExpr) (e' : KExpr) (T : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') (ht : has_type e T) => whnf_to_preserves_typing hf e e' T wd wr (kernel_whnf_reduces_to_spec_whnf st e e' henv hctx hin haccept) ht".to_string()),
            is_axiom: false,
            description: "Derived simulation corollary: kernel WHNF preserves typing because its output is the DIRECTED whnf_to reduct of the input. Reroutes through whnf_to_preserves_typing ∘ kernel_whnf_reduces_to_spec_whnf (genuine subject reduction over the directed trace — no raw-DefEq subject expansion). church_rosser_whnf retirement track.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to_preserves_typing".to_string(),
                "kernel_whnf_reduces_to_spec_whnf".to_string(),
            ])),
            // whnf_to_preserves_typing now re-points off church_rosser_whnf via
            // join_to_def_eq / RedEnvFaithful; no residual axiom leaf.
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Summary-alias forward simulation wrappers
        // =========================================================
        //
        // These take KernelStateMatchesSpec st (the summary) instead of the
        // split predicates, using the eliminators to decompose.

        self.add_definition(SpecDefinition {
            name: "KernelInferSound_summary".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (T : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelInferAccepts st e T -> has_type e T".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (T : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelInferAccepts st e T) => KernelInferSound st e T (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept".to_string()),
            is_axiom: false,
            description: "Forward simulation for infer_type via the summary alias: decomposes KernelStateMatchesSpec into its split predicates and delegates to KernelInferSound.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferSound".to_string(),
                "KernelStateMatchesSpec.envValid".to_string(),
                "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            ])),
            axiom_deps: HashSet::from([
                // Keep the named dispatcher edge for existing summary-layer
                // audits, but also surface the actual infer leaf obligations.
                // The six per-case infer axioms are no longer leaves (derived
                // via kernel_infer_inversion); the residual is the master
                // inversion's closure (10 infer-band skolems +
                // KernelCheckAccepts) plus the check/defeq band.
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelCheckSound_summary".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (T : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelCheckAccepts st e T -> has_type e T".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (T : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelCheckAccepts st e T) => KernelCheckSound st e T (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept".to_string()),
            is_axiom: false,
            description: "Forward simulation for check_type via the summary alias: decomposes KernelStateMatchesSpec into its split predicates and delegates to KernelCheckSound.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelCheckSound".to_string(),
                "KernelStateMatchesSpec.envValid".to_string(),
                "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            ])),
            // Expands through DerivedLemma KernelCheckSound to the check band,
            // which since Step 4 expands through the faithful KernelCheckAccepts
            // inductive to the skolem-witness closure.
            // kernel_def_eq_reflects_spec further expands to the two defeq
            // normal-form skolems.
            axiom_deps: HashSet::from([
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelWhnfSound_summary".to_string(),
            type_src: "forall (st : KernelState) (e : KExpr) (e' : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelWhnfAccepts st e e' -> is_def_eq e e'".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) (e' : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') => KernelWhnfSound st e e' (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept".to_string()),
            is_axiom: false,
            description: "Forward simulation for whnf via the summary alias: decomposes KernelStateMatchesSpec into its split predicates and delegates to KernelWhnfSound.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelWhnfSound".to_string(),
                "KernelStateMatchesSpec.envValid".to_string(),
                "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelDefEqSound_summary".to_string(),
            type_src: "forall (st : KernelState) (a : KExpr) (b : KExpr), KernelStateMatchesSpec st -> KernelBinaryInputAdmissible st a b -> KernelDefEqAccepts st a b -> is_def_eq a b".to_string(),
            value_src: Some("fun (st : KernelState) (a : KExpr) (b : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelBinaryInputAdmissible st a b) (haccept : KernelDefEqAccepts st a b) => KernelDefEqSound st a b (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept".to_string()),
            is_axiom: false,
            description: "Forward simulation for is_def_eq via the summary alias: decomposes KernelStateMatchesSpec into its split predicates and delegates to KernelDefEqSound.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelDefEqSound".to_string(),
                "KernelStateMatchesSpec.envValid".to_string(),
                "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            ])),
            // kernel_def_eq_reflects_spec is now skolem-free (KernelDefEqAccepts.mk
            // concludes in the non-axiom DefEqJoinable existential), so no residual leaf.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_simulation_tests.rs"]
mod implementation_soundness_simulation_tests;
