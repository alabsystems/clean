// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! KExpr Pi constructor discrimination and injectivity (PART 4b extension).
//!
//! Extends the App discrimination/injectivity from `expr_model_discrimination.rs`
//! with analogous infrastructure for the Pi constructor. Enables typing
//! inversion proofs for `pi_type_preservation`.
//!
//! Part of #464: Phase 4A constructive derivation — typing inversion for
//! converting pi congruence case helpers from HelperAxiom to DerivedProved.
//!
//! NOTE: Same design as the App file — proof terms inline KExpr.rec rather than
//! referencing named Opaque definitions.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline KExpr.rec discriminator: non-Pi -> Nat, Pi -> Empty.
const KEXPR_NOT_PI_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_expr_model_pi_discrimination(&mut self) -> Result<(), SpecError> {
        self.add_pi_discr_base()?;
        self.add_pi_discr_ne()?;
        self.add_pi_inj_projections()?;
        self.add_pi_inj_proofs()?;
        Ok(())
    }

    fn add_pi_discr_base(&mut self) -> Result<(), SpecError> {
        // kexpr_not_pi : KExpr -> Type
        // Maps non-Pi constructors to Nat, Pi to Empty.
        self.add_definition(SpecDefinition {
            name: "kexpr_not_pi".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "KExpr.rec (fun (_ : KExpr) => Type) ",
                    "(fun (_ : Level) => Nat) ",
                    "(fun (_ : Nat) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
                    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
                    "(fun (_ : Nat) => Nat)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Large-elimination discriminator: non-Pi -> Nat, Pi -> Empty. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // sort_ne_pi: Sort n ≠ Pi A B
        self.add_definition(SpecDefinition {
            name: "sort_ne_pi".to_string(),
            type_src: "forall (n : Level) (A : KExpr) (B : KExpr) (R : Type), Eq KExpr (KExpr.sort n) (KExpr.pi A B) -> R".to_string(),
            value_src: Some(format!(
                "fun (n : Level) (A : KExpr) (B : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.sort n) (KExpr.pi A B)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.pi A B) h Nat.zero)",
                discr = KEXPR_NOT_PI_INLINE,
            )),
            is_axiom: false,
            description: "Sort ≠ Pi discrimination. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_pi_discr_ne(&mut self) -> Result<(), SpecError> {
        // app_ne_pi: App f a ≠ Pi A B
        self.add_definition(SpecDefinition {
            name: "app_ne_pi".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (R : Type), Eq KExpr (KExpr.app f a) (KExpr.pi A B) -> R".to_string(),
            value_src: Some(format!(
                "fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.app f a) (KExpr.pi A B)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.app f a) (KExpr.pi A B) h Nat.zero)",
                discr = KEXPR_NOT_PI_INLINE,
            )),
            is_axiom: false,
            description: "App ≠ Pi discrimination. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lam_ne_pi: Lam A0 b0 ≠ Pi A B
        self.add_definition(SpecDefinition {
            name: "lam_ne_pi".to_string(),
            type_src: "forall (A0 : KExpr) (b0 : KExpr) (A : KExpr) (B : KExpr) (R : Type), Eq KExpr (KExpr.lam A0 b0) (KExpr.pi A B) -> R".to_string(),
            value_src: Some(format!(
                "fun (A0 : KExpr) (b0 : KExpr) (A : KExpr) (B : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.lam A0 b0) (KExpr.pi A B)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.lam A0 b0) (KExpr.pi A B) h Nat.zero)",
                discr = KEXPR_NOT_PI_INLINE,
            )),
            is_axiom: false,
            description: "Lam ≠ Pi discrimination. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_pi_inj_projections(&mut self) -> Result<(), SpecError> {
        // pi_fst: extract domain from Pi (default for non-Pi)
        self.add_definition(SpecDefinition {
            name: "pi_fst".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (default : KExpr) => ",
                    "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (A : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A) ",
                    "(fun (_ : Name) (_ : ListType Level) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "e"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Extract domain from Pi, or return default. pi_fst (Pi A B) d = A. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // pi_snd: extract codomain from Pi (default for non-Pi)
        self.add_definition(SpecDefinition {
            name: "pi_snd".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (default : KExpr) => ",
                    "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : KExpr) (B : KExpr) (_ : KExpr) (_ : KExpr) => B) ",
                    "(fun (_ : Name) (_ : ListType Level) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "e"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Extract codomain from Pi, or return default. pi_snd (Pi A B) d = B. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_pi_inj_proofs(&mut self) -> Result<(), SpecError> {
        self.add_pi_inj_base_proofs()
    }

    fn add_pi_inj_base_proofs(&mut self) -> Result<(), SpecError> {
        // pi_inj_fst: Pi A1 B1 = Pi A2 B2 -> A1 = A2
        self.add_definition(SpecDefinition {
            name: "pi_inj_fst".to_string(),
            type_src: "forall (A1 : KExpr) (B1 : KExpr) (A2 : KExpr) (B2 : KExpr), Eq KExpr (KExpr.pi A1 B1) (KExpr.pi A2 B2) -> Eq KExpr A1 A2".to_string(),
            value_src: Some(
                "fun (A1 : KExpr) (B1 : KExpr) (A2 : KExpr) (B2 : KExpr) \
                 (h : Eq KExpr (KExpr.pi A1 B1) (KExpr.pi A2 B2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => A1) \
                   (fun (_ : Nat) => A1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (dom : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => dom) \
                   (fun (_ : Name) (_ : ListType Level) => A1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : Nat) => A1) \
                   e) \
                 (KExpr.pi A1 B1) (KExpr.pi A2 B2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Pi injectivity (fst): Pi A1 B1 = Pi A2 B2 -> A1 = A2. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // pi_inj_snd: Pi A1 B1 = Pi A2 B2 -> B1 = B2
        self.add_definition(SpecDefinition {
            name: "pi_inj_snd".to_string(),
            type_src: "forall (A1 : KExpr) (B1 : KExpr) (A2 : KExpr) (B2 : KExpr), Eq KExpr (KExpr.pi A1 B1) (KExpr.pi A2 B2) -> Eq KExpr B1 B2".to_string(),
            value_src: Some(
                "fun (A1 : KExpr) (B1 : KExpr) (A2 : KExpr) (B2 : KExpr) \
                 (h : Eq KExpr (KExpr.pi A1 B1) (KExpr.pi A2 B2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => B1) \
                   (fun (_ : Nat) => B1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => B1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => B1) \
                   (fun (_ : KExpr) (cod : KExpr) (_ : KExpr) (_ : KExpr) => cod) \
                   (fun (_ : Name) (_ : ListType Level) => B1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => B1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => B1) \
                   (fun (_ : Nat) => B1) \
                   e) \
                 (KExpr.pi A1 B1) (KExpr.pi A2 B2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Pi injectivity (snd): Pi A1 B1 = Pi A2 B2 -> B1 = B2. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}
