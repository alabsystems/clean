// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Derived typing and def-eq rules as backward-compatible aliases (PARTs 6-8)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_derived_rules(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 6: (Reserved) - TypePreservation moved to PART 12.5
        // =========================================================
        // TypePreservation is defined after PART 12 (type preservation infrastructure)
        // because its proof term references def_eq_preserves_typing from that section.

        // =========================================================
        // PART 7: Typing Rules as Derived Definitions
        // =========================================================
        //
        // These rules are now derived from the Typing inductive constructors.
        // They provide backward-compatible names that reference Typing.*.
        // Part of #351: substitution_typing needs inductive has_type

        // Sort typing rule: Sort n : Sort (n + 1)
        // DerivedLemma: Defined from Typing.sort constructor
        self.add_definition(SpecDefinition {
            name: "sort_typing".to_string(),
            type_src: "forall (n : Level), Typing (KExpr.sort n) (KExpr.sort (Level.succ n))"
                .to_string(),
            value_src: Some("fun (n : Level) => Typing.sort n".to_string()),
            is_axiom: false,
            description: "Sort typing rule: Sort n has type Sort (n+1). Derived from Typing.sort."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Pi formation rule
        // DerivedLemma: Defined from Typing.pi constructor
        // Part of #2870: result sort now uses imax_nat n m instead of m
        self.add_definition(SpecDefinition {
            name: "pi_formation".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr) (n : Level) (m : Level), Typing A (KExpr.sort n) -> Typing B (KExpr.sort m) -> Typing (KExpr.pi A B) (KExpr.sort (Level.imax n m))".to_string(),
            value_src: Some("fun (A : KExpr) (B : KExpr) (n : Level) (m : Level) (hA : Typing A (KExpr.sort n)) (hB : Typing B (KExpr.sort m)) => Typing.pi A B n m hA hB".to_string()),
            is_axiom: false,
            description: "Pi formation: if A : Sort n and B : Sort m, then (A -> B) : Sort (imax n m). Derived from Typing.pi. Part of #2870.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Lambda typing rule
        // DerivedLemma: Defined from Typing.lam constructor
        // Part of #2870: domain universe now parameterized by u instead of hardcoded Nat.zero
        self.add_definition(SpecDefinition {
            name: "lam_typing".to_string(),
            type_src: "forall (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), Typing A (KExpr.sort u) -> Typing b B -> Typing (KExpr.lam A b) (KExpr.pi A B)".to_string(),
            value_src: Some("fun (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) (hA : Typing A (KExpr.sort u)) (hb : Typing b B) => Typing.lam A b B u hA hb".to_string()),
            is_axiom: false,
            description: "Lambda typing: if A : Sort u and b : B, then (λA.b) : (A → B). Derived from Typing.lam. Part of #2870.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Application typing rule (dependent)
        // DerivedLemma: Defined from Typing.app constructor
        // Part of #464: updated to dependent rule (instantiate B a).
        self.add_definition(SpecDefinition {
            name: "app_typing".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), Typing f (KExpr.pi A B) -> Typing a A -> Typing (KExpr.app f a) (instantiate B a)".to_string(),
            value_src: Some("fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (hf : Typing f (KExpr.pi A B)) (ha : Typing a A) => Typing.app f a A B hf ha".to_string()),
            is_axiom: false,
            description: "Application typing (dependent): if f : Π(A,B) and a : A, then (f a) : B[a/0]. Derived from Typing.app. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 8: Definitional Equality Rules (Backward-Compatible Aliases)
        // =========================================================
        // These are now derived from DefEq constructors for backward compatibility.
        // New code should use DefEq.refl, DefEq.symm, etc. directly.

        // Reflexivity of def eq (alias for DefEq.refl)
        self.add_definition(SpecDefinition {
            name: "def_eq_refl".to_string(),
            type_src: "forall (e : KExpr), DefEq e e".to_string(),
            value_src: Some("fun (e : KExpr) => DefEq.refl e".to_string()),
            is_axiom: false,
            description: "Definitional equality is reflexive (alias for DefEq.refl).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Symmetry of def eq (alias for DefEq.symm)
        self.add_definition(SpecDefinition {
            name: "def_eq_symm".to_string(),
            type_src: "forall (a : KExpr) (b : KExpr), DefEq a b -> DefEq b a".to_string(),
            value_src: Some(
                "fun (a : KExpr) (b : KExpr) (h : DefEq a b) => DefEq.symm a b h".to_string(),
            ),
            is_axiom: false,
            description: "Definitional equality is symmetric (alias for DefEq.symm).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Transitivity of def eq (alias for DefEq.trans)
        self.add_definition(SpecDefinition {
            name: "def_eq_trans".to_string(),
            type_src: "forall (a : KExpr) (b : KExpr) (c : KExpr), DefEq a b -> DefEq b c -> DefEq a c".to_string(),
            value_src: Some("fun (a : KExpr) (b : KExpr) (c : KExpr) (hab : DefEq a b) (hbc : DefEq b c) => DefEq.trans a b c hab hbc".to_string()),
            is_axiom: false,
            description: "Definitional equality is transitive (alias for DefEq.trans).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Beta reduction (alias for DefEq.beta, typed)
        self.add_definition(SpecDefinition {
            name: "beta_reduction".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (b : KExpr) (a : KExpr) (B : KExpr) (u : Level), ",
                "Typing A (KExpr.sort u) -> Typing b B -> Typing a A -> ",
                "DefEq (KExpr.app (KExpr.lam A b) a) (instantiate b a)"
            ).to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (b : KExpr) (a : KExpr) (_B : KExpr) (_u : Level) ",
                "(_hA : Typing A (KExpr.sort _u)) (_hb : Typing b _B) (_ha : Typing a A) => ",
                "DefEq.beta A b a"
            ).to_string()),
            is_axiom: false,
            description: "Typed beta reduction: (λA.b) a ≡ b[a/0] with typing premises (alias for DefEq.beta). Part of #2872.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["DefEq.beta".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // def_eq_to_eq (the FALSE `forall a b, DefEq a b -> Eq a b` bridge) was
        // DELETED in Brick 9 (#2859): every consumer is rerouted onto Typing.conv
        // (untyped conversion) or the constructive sort_def_eq_eq / def_eq_respects_lift_at
        // confluence tower, so the value-less PendingLeaf axiom is gone entirely.

        Ok(())
    }
}
