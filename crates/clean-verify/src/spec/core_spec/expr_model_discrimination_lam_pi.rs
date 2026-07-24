// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! KExpr Lam constructor discrimination and injectivity (PART 4b extension).
//!
//! Extends the App discrimination/injectivity from `expr_model_discrimination.rs`
//! with analogous infrastructure for the Lam constructor. Enables typing
//! inversion proofs for `lam_type_preservation`.
//!
//! Part of #464: Phase 4A constructive derivation — typing inversion for
//! converting lam congruence case helpers from HelperAxiom to DerivedProved.
//!
//! NOTE: Same design as the App file — proof terms inline KExpr.rec rather than
//! referencing named Opaque definitions.
//!
//! Pi discrimination is in `expr_model_discrimination_pi.rs`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline KExpr.rec discriminator: non-Lam -> Nat, Lam -> Empty.
const KEXPR_NOT_LAM_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_expr_model_lam_discrimination(&mut self) -> Result<(), SpecError> {
        self.add_lam_discr_base()?;
        self.add_lam_discr_ne()?;
        self.add_lam_inj_projections()?;
        self.add_lam_inj_proofs()?;
        Ok(())
    }

    fn add_lam_discr_base(&mut self) -> Result<(), SpecError> {
        // kexpr_not_lam : KExpr -> Type
        // Maps non-Lam constructors to Nat, Lam to Empty.
        self.add_definition(SpecDefinition {
            name: "kexpr_not_lam".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "KExpr.rec (fun (_ : KExpr) => Type) ",
                    "(fun (_ : Level) => Nat) ",
                    "(fun (_ : Nat) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
                    "(fun (_ : Nat) => Nat)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Large-elimination discriminator: non-Lam -> Nat, Lam -> Empty. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // sort_ne_lam: Sort n ≠ Lam A b
        self.add_definition(SpecDefinition {
            name: "sort_ne_lam".to_string(),
            type_src: "forall (n : Level) (A : KExpr) (b : KExpr) (R : Type), Eq KExpr (KExpr.sort n) (KExpr.lam A b) -> R".to_string(),
            value_src: Some(format!(
                "fun (n : Level) (A : KExpr) (b : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.sort n) (KExpr.lam A b)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.lam A b) h Nat.zero)",
                discr = KEXPR_NOT_LAM_INLINE,
            )),
            is_axiom: false,
            description: "Sort ≠ Lam discrimination. Part of #464.".to_string(),
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

    fn add_lam_discr_ne(&mut self) -> Result<(), SpecError> {
        // app_ne_lam: App f a ≠ Lam A b
        self.add_definition(SpecDefinition {
            name: "app_ne_lam".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (A : KExpr) (b : KExpr) (R : Type), Eq KExpr (KExpr.app f a) (KExpr.lam A b) -> R".to_string(),
            value_src: Some(format!(
                "fun (f : KExpr) (a : KExpr) (A : KExpr) (b : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.app f a) (KExpr.lam A b)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.app f a) (KExpr.lam A b) h Nat.zero)",
                discr = KEXPR_NOT_LAM_INLINE,
            )),
            is_axiom: false,
            description: "App ≠ Lam discrimination. Part of #464.".to_string(),
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

        // pi_ne_lam: Pi A0 B0 ≠ Lam A b
        self.add_definition(SpecDefinition {
            name: "pi_ne_lam".to_string(),
            type_src: "forall (A0 : KExpr) (B0 : KExpr) (A : KExpr) (b : KExpr) (R : Type), Eq KExpr (KExpr.pi A0 B0) (KExpr.lam A b) -> R".to_string(),
            value_src: Some(format!(
                "fun (A0 : KExpr) (B0 : KExpr) (A : KExpr) (b : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.pi A0 B0) (KExpr.lam A b)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.pi A0 B0) (KExpr.lam A b) h Nat.zero)",
                discr = KEXPR_NOT_LAM_INLINE,
            )),
            is_axiom: false,
            description: "Pi ≠ Lam discrimination. Part of #464.".to_string(),
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

    fn add_lam_inj_projections(&mut self) -> Result<(), SpecError> {
        // lam_fst: extract domain from Lam (default for non-Lam)
        self.add_definition(SpecDefinition {
            name: "lam_fst".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (default : KExpr) => ",
                    "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (A : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
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
                "Extract domain from Lam, or return default. lam_fst (Lam A b) d = A. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // lam_snd: extract body from Lam (default for non-Lam)
        self.add_definition(SpecDefinition {
            name: "lam_snd".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (default : KExpr) => ",
                    "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                    "(fun (_ : Level) => default) ",
                    "(fun (_ : Nat) => default) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                    "(fun (_ : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) => b) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
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
                "Extract body from Lam, or return default. lam_snd (Lam A b) d = b. Part of #464."
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

    fn add_lam_inj_proofs(&mut self) -> Result<(), SpecError> {
        // lam_inj_fst: Lam A1 b1 = Lam A2 b2 -> A1 = A2
        self.add_definition(SpecDefinition {
            name: "lam_inj_fst".to_string(),
            type_src: "forall (A1 : KExpr) (b1 : KExpr) (A2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.lam A1 b1) (KExpr.lam A2 b2) -> Eq KExpr A1 A2".to_string(),
            value_src: Some(
                "fun (A1 : KExpr) (b1 : KExpr) (A2 : KExpr) (b2 : KExpr) \
                 (h : Eq KExpr (KExpr.lam A1 b1) (KExpr.lam A2 b2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => A1) \
                   (fun (_ : Nat) => A1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (dom : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => dom) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : Name) (_ : ListType Level) => A1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => A1) \
                   (fun (_ : Nat) => A1) \
                   e) \
                 (KExpr.lam A1 b1) (KExpr.lam A2 b2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Lam injectivity (fst): Lam A1 b1 = Lam A2 b2 -> A1 = A2. Part of #464.".to_string(),
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

        // lam_inj_snd: Lam A1 b1 = Lam A2 b2 -> b1 = b2
        self.add_definition(SpecDefinition {
            name: "lam_inj_snd".to_string(),
            type_src: "forall (A1 : KExpr) (b1 : KExpr) (A2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.lam A1 b1) (KExpr.lam A2 b2) -> Eq KExpr b1 b2".to_string(),
            value_src: Some(
                "fun (A1 : KExpr) (b1 : KExpr) (A2 : KExpr) (b2 : KExpr) \
                 (h : Eq KExpr (KExpr.lam A1 b1) (KExpr.lam A2 b2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => b1) \
                   (fun (_ : Nat) => b1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) \
                   (fun (_ : KExpr) (body : KExpr) (_ : KExpr) (_ : KExpr) => body) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) \
                   (fun (_ : Name) (_ : ListType Level) => b1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => b1) \
                   (fun (_ : Nat) => b1) \
                   e) \
                 (KExpr.lam A1 b1) (KExpr.lam A2 b2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Lam injectivity (snd): Lam A1 b1 = Lam A2 b2 -> b1 = b2. Part of #464.".to_string(),
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
