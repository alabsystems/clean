// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Type preservation infrastructure and theorem (PARTs 12, 12.3, 12.5, 13)
//!
//! The case helpers and def_eq_typing_iff proof term are in
//! `type_preservation_cases.rs` (PART 12 internals).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_type_preservation(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 12: Type Preservation Infrastructure
        // =========================================================
        // Registration order: substitution_typing + type_conversion first,
        // then Eq specializers consumed by the case helpers, then case helpers
        // + def_eq_typing_iff (in type_preservation_cases.rs), then derived
        // lemmas and the TypePreservation theorem.

        // Substitution typing (in type_preservation_subst.rs):
        // substitution_typing_gen, substitution_typing, def_eq_instantiate_arg_congr
        self.add_type_preservation_subst()?;

        // Packet A Eq specializers. `typing_same_term_types_def_eq` uses
        // sort_def_eq_eq in its Pi case, so these must register before the case
        // helper block below.
        self.add_type_preservation_eq_specializers()?;

        // Type conversion — DerivedProved via Typing.conv.
        // The proof applies the foundational Typing.conv constructor directly.
        // Previously blocked on the Opaque alias barrier (has_type↔Typing and
        // is_def_eq↔DefEq). Now unblocked: both aliases are registered as
        // reducible Definitions. Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "type_conversion".to_string(),
            type_src: "forall (e : KExpr) (T1 : KExpr) (T2 : KExpr), has_type e T1 -> typing_is_def_eq T1 T2 -> has_type e T2".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(ht : has_type e T1) (heq : typing_is_def_eq T1 T2) => ",
                "Typing.conv e T1 T2 ht (typed_def_eq_to_def_eq T1 T2 heq)"
            ).to_string()),
            is_axiom: false,
            description: "Type conversion: if e : T1 and T1 ≡ T2 in the typed conversion lane, then e : T2. Proof via Typing.conv. Part of #2872.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Register generation lemmas (in type_preservation_generation.rs)
        // These are needed before typing_same_term_types_def_eq.
        self.add_type_preservation_generation()?;

        // Register case helpers + def_eq_typing_iff (in type_preservation_cases.rs)
        self.add_type_preservation_cases()?;

        // =========================================================
        // PART 12.3: Derived lemmas from def_eq_typing_iff
        // =========================================================

        // Def eq preserves typing — DerivedPending via def_eq_typing_iff.
        // The proof extracts the forward direction from the bidirectional AndType result.
        // Previously blocked on the Opaque alias barrier (is_def_eq was registered as
        // Declaration::Opaque, preventing kernel defEq from seeing is_def_eq = DefEq).
        // Now unblocked: is_def_eq and has_type are registered as reducible Definitions,
        // so the kernel can unfold them during type checking.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "def_eq_preserves_typing".to_string(),
            type_src: "forall (hf : RedEnvFaithful the_red_env) (e : KExpr) (e' : KExpr) (T : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> has_type e T -> typing_is_def_eq e e' -> has_type e' T".to_string(),
            value_src: Some(concat!(
                "fun (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr) (T : KExpr) ",
                "(wd : DefEnvWellformed the_red_env) ",
                "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                "(ht : has_type e T) (heq : typing_is_def_eq e e') => ",
                "AndType.left ",
                "(forall (T : KExpr), has_type e T -> has_type e' T) ",
                "(forall (T : KExpr), has_type e' T -> has_type e T) ",
                "(def_eq_typing_iff hf e e' wd wr heq) T ht"
            ).to_string()),
            is_axiom: false,
            description: concat!(
                "Typed definitional equality preserves typing (type preservation). ",
                "Proof: AndType.left (def_eq_typing_iff e e' heq) T ht. ",
                "The primary typing theorem now lives on typing_is_def_eq. Part of #2872."
            ).to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            // pi_injectivity_def_eq now DerivedProved via church_rosser_whnf (#2851).
            // delta/iota helpers DerivedProved via #725 reduction witnesses.
            // typing_same_term_types_def_eq now DerivedPending via church_rosser_whnf (#461).
            // Transitive HelperAxiom frontier via def_eq_typing_iff.
            // Part of #464.
            axiom_deps: HashSet::new(),
        })?;

        // Congruence for application (alias for DefEq.app_cong)
        self.add_definition(SpecDefinition {
            name: "def_eq_app_cong".to_string(),
            type_src: "forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), DefEq f f' -> DefEq a a' -> DefEq (KExpr.app f a) (KExpr.app f' a')".to_string(),
            value_src: Some("fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (hf : DefEq f f') (ha : DefEq a a') => DefEq.app_cong f f' a a' hf ha".to_string()),
            is_axiom: false,
            description: "Application congruence for def eq (alias for DefEq.app_cong).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Congruence for lambda (simplified: keeps A the same)
        self.add_definition(SpecDefinition {
            name: "def_eq_lam_cong".to_string(),
            type_src: "forall (A : KExpr) (b : KExpr) (b' : KExpr), DefEq b b' -> DefEq (KExpr.lam A b) (KExpr.lam A b')".to_string(),
            value_src: Some("fun (A : KExpr) (b : KExpr) (b' : KExpr) (hb : DefEq b b') => DefEq.lam_cong A A b b' (DefEq.refl A) hb".to_string()),
            is_axiom: false,
            description: "Lambda congruence for def eq (derived from DefEq.lam_cong with A ≡ A).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Congruence for pi (alias for DefEq.pi_cong)
        self.add_definition(SpecDefinition {
            name: "def_eq_pi_cong".to_string(),
            type_src: "forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), DefEq A A' -> DefEq B B' -> DefEq (KExpr.pi A B) (KExpr.pi A' B')".to_string(),
            value_src: Some("fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (hA : DefEq A A') (hB : DefEq B B') => DefEq.pi_cong A A' B B' hA hB".to_string()),
            is_axiom: false,
            description: "Pi congruence for def eq (alias for DefEq.pi_cong).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 12.5: Type Preservation Theorem
        // =========================================================

        // TypePreservation: forwards to def_eq_preserves_typing (now DerivedPending).
        // Previously both shared the is_def_eq Opaque barrier. Now unblocked:
        // def_eq_preserves_typing has a proof term, and TypePreservation forwards to it.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "TypePreservation".to_string(),
            type_src: "forall (hf : RedEnvFaithful the_red_env) (e : KExpr) (T : KExpr) (e' : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> has_type e T -> typing_is_def_eq e e' -> has_type e' T".to_string(),
            value_src: Some("fun (hf : RedEnvFaithful the_red_env) (e : KExpr) (T : KExpr) (e' : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (ht : has_type e T) (heq : typing_is_def_eq e e') => def_eq_preserves_typing hf e e' T wd wr ht heq".to_string()),
            is_axiom: false,
            description: "Type preservation: if e : T and e ≡ e' in the typed conversion lane, then e' : T. Forwards to def_eq_preserves_typing.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            // Transitive HelperAxiom frontier via def_eq_preserves_typing.
            // Part of #464.
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 13: Derived typing lemmas (concrete programs)
        // =========================================================

        self.add_definition(SpecDefinition {
            name: "identity_typing".to_string(),
            type_src: "forall (A : Type), A -> A".to_string(),
            value_src: Some("fun (A : Type) (x : A) => x".to_string()),
            is_axiom: false,
            description: "The identity function has type A → A.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "const_typing".to_string(),
            type_src: "forall (A : Type) (B : Type), A -> B -> A".to_string(),
            value_src: Some("fun (A : Type) (B : Type) (a : A) (_b : B) => a".to_string()),
            is_axiom: false,
            description: "The const function has type A → B → A.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "compose_typing".to_string(),
            type_src: "forall (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B), A -> C"
                .to_string(),
            value_src: Some(
                "fun (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B) (x : A) => g (f x)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Function composition has type (B→C) → (A→B) → A → C.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "flip_typing".to_string(),
            type_src: "forall (A : Type) (B : Type) (C : Type) (f : A -> B -> C), B -> A -> C"
                .to_string(),
            value_src: Some(
                "fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) => f a b"
                    .to_string(),
            ),
            is_axiom: false,
            description: "The flip combinator swaps function arguments.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "type_preservation_typed_lane_tests.rs"]
mod type_preservation_typed_lane_tests;

#[cfg(test)]
#[path = "type_preservation_chain_status_tests.rs"]
mod type_preservation_chain_status_tests;
