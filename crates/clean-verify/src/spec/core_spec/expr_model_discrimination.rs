// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! KExpr constructor discrimination and App injectivity (PART 4b).
//!
//! Provides the infrastructure needed for typing inversion proofs:
//! - `kexpr_not_app`: large-elimination discriminator (KExpr -> Type via KExpr.rec)
//! - `sort_ne_app`, `lam_ne_app`, `pi_ne_app`: constructor discrimination
//! - `app_fst`, `app_snd`: App component extraction (KExpr.rec)
//! - `app_inj_fst`, `app_inj_snd`: App constructor injectivity
//!
//! Part of #464: Phase 4A constructive derivation — typing inversion for
//! converting congruence case helpers from HelperAxiom to DerivedProved.
//!
//! NOTE: Proof terms inline KExpr.rec rather than referencing the named
//! definitions (kexpr_not_app, app_fst, app_snd) because those are registered
//! as Opaque and the elaborator cannot delta-unfold them. The elaborator CAN
//! do iota reduction on KExpr.rec directly, so inlining works.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline KExpr.rec discriminator: non-App -> Nat, App -> Empty.
/// Used in discrimination proof terms (sort_ne_app, lam_ne_app, pi_ne_app).
const KEXPR_NOT_APP_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_expr_model_discrimination(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // KExpr constructor discrimination via large elimination
        // =========================================================
        //
        // kexpr_not_app : KExpr -> Type
        // Maps non-App constructors to Nat (inhabited, in Type/Sort 1)
        // and App to Empty (uninhabited, in Type/Sort 1).
        //
        // This uses large elimination (KExpr.rec with Type-valued motive).
        // Justified: KExpr is in Type (not Prop), so large elimination is valid CIC.
        // Uses Nat/Empty (both in Sort 1) to avoid Sort 2 universe conflicts
        // that arise with forall-quantified types.
        self.add_definition(SpecDefinition {
            name: "kexpr_not_app".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(concat!(
                "KExpr.rec (fun (_ : KExpr) => Type) ",
                "(fun (_ : Level) => Nat) ",
                "(fun (_ : Nat) => Nat) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                "(fun (_ : Name) (_ : ListType Level) => Nat) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
                "(fun (_ : Nat) => Nat)"
            ).to_string()),
            is_axiom: false,
            description: "Large-elimination discriminator: non-App constructors map to Nat (inhabited), App maps to Empty (uninhabited). Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // sort_ne_app: Sort n ≠ App f a
        // Proof: Eq.substType transports Nat.zero through the inline discriminator
        // to get Empty, then Empty.rec produces any R.
        // Inlines KExpr.rec because kexpr_not_app is Opaque.
        self.add_definition(SpecDefinition {
            name: "sort_ne_app".to_string(),
            type_src: "forall (n : Level) (f : KExpr) (a : KExpr) (R : Type), Eq KExpr (KExpr.sort n) (KExpr.app f a) -> R".to_string(),
            value_src: Some(format!(
                "fun (n : Level) (f : KExpr) (a : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.sort n) (KExpr.app f a)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.app f a) h Nat.zero)",
                discr = KEXPR_NOT_APP_INLINE,
            )),
            is_axiom: false,
            description: "Sort ≠ App discrimination. Derived via Eq.substType + inline discriminator + Empty.rec. Part of #464.".to_string(),
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

        // lam_ne_app: Lam A b ≠ App f a
        self.add_definition(SpecDefinition {
            name: "lam_ne_app".to_string(),
            type_src: "forall (A : KExpr) (b : KExpr) (f : KExpr) (a : KExpr) (R : Type), Eq KExpr (KExpr.lam A b) (KExpr.app f a) -> R".to_string(),
            value_src: Some(format!(
                "fun (A : KExpr) (b : KExpr) (f : KExpr) (a : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.lam A b) (KExpr.app f a)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.lam A b) (KExpr.app f a) h Nat.zero)",
                discr = KEXPR_NOT_APP_INLINE,
            )),
            is_axiom: false,
            description: "Lam ≠ App discrimination. Derived via Eq.substType + inline discriminator + Empty.rec. Part of #464.".to_string(),
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

        // pi_ne_app: Pi A B ≠ App f a
        self.add_definition(SpecDefinition {
            name: "pi_ne_app".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) (R : Type), Eq KExpr (KExpr.pi A B) (KExpr.app f a) -> R".to_string(),
            value_src: Some(format!(
                "fun (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) (R : Type) \
                 (h : Eq KExpr (KExpr.pi A B) (KExpr.app f a)) => \
                 Empty.rec (fun (_ : Empty) => R) \
                 (Eq.substType KExpr {discr} (KExpr.pi A B) (KExpr.app f a) h Nat.zero)",
                discr = KEXPR_NOT_APP_INLINE,
            )),
            is_axiom: false,
            description: "Pi ≠ App discrimination. Derived via Eq.substType + inline discriminator + Empty.rec. Part of #464.".to_string(),
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

        // =========================================================
        // App component extraction and injectivity
        // =========================================================

        // app_fst: extract function component from App (returns default for non-App)
        self.add_definition(SpecDefinition {
            name: "app_fst".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (default : KExpr) => ",
                "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => default) ",
                "(fun (_ : Nat) => default) ",
                "(fun (f : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => f) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Name) (_ : ListType Level) => default) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Nat) => default) ",
                "e"
            ).to_string()),
            is_axiom: false,
            description: "Extract function from App, or return default. app_fst (App f a) d = f. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // app_snd: extract argument component from App (returns default for non-App)
        self.add_definition(SpecDefinition {
            name: "app_snd".to_string(),
            type_src: "forall (e : KExpr) (default : KExpr), KExpr".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (default : KExpr) => ",
                "KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => default) ",
                "(fun (_ : Nat) => default) ",
                "(fun (_ : KExpr) (a : KExpr) (_ : KExpr) (_ : KExpr) => a) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Name) (_ : ListType Level) => default) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => default) ",
                "(fun (_ : Nat) => default) ",
                "e"
            ).to_string()),
            is_axiom: false,
            description: "Extract argument from App, or return default. app_snd (App f a) d = a. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // app_inj_fst: App f1 a1 = App f2 a2 -> f1 = f2
        // Proof: Eq.cong with inline app_fst KExpr.rec, using f1 as default.
        // Inlines KExpr.rec because app_fst is Opaque.
        self.add_definition(SpecDefinition {
            name: "app_inj_fst".to_string(),
            type_src: "forall (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr), Eq KExpr (KExpr.app f1 a1) (KExpr.app f2 a2) -> Eq KExpr f1 f2".to_string(),
            value_src: Some(
                "fun (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr) \
                 (h : Eq KExpr (KExpr.app f1 a1) (KExpr.app f2 a2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => f1) \
                   (fun (_ : Nat) => f1) \
                   (fun (fn_expr : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => fn_expr) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => f1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => f1) \
                   (fun (_ : Name) (_ : ListType Level) => f1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => f1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => f1) \
                   (fun (_ : Nat) => f1) \
                   e) \
                 (KExpr.app f1 a1) (KExpr.app f2 a2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "App injectivity (fst): App f1 a1 = App f2 a2 -> f1 = f2. Part of #464.".to_string(),
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

        // app_inj_snd: App f1 a1 = App f2 a2 -> a1 = a2
        // Proof: Eq.cong with inline app_snd KExpr.rec, using a1 as default.
        self.add_definition(SpecDefinition {
            name: "app_inj_snd".to_string(),
            type_src: "forall (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr), Eq KExpr (KExpr.app f1 a1) (KExpr.app f2 a2) -> Eq KExpr a1 a2".to_string(),
            value_src: Some(
                "fun (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr) \
                 (h : Eq KExpr (KExpr.app f1 a1) (KExpr.app f2 a2)) => \
                 Eq.cong KExpr KExpr \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                   (fun (_ : Level) => a1) \
                   (fun (_ : Nat) => a1) \
                   (fun (_ : KExpr) (arg_expr : KExpr) (_ : KExpr) (_ : KExpr) => arg_expr) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => a1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => a1) \
                   (fun (_ : Name) (_ : ListType Level) => a1) \
                   (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => a1) \
                   (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => a1) \
                   (fun (_ : Nat) => a1) \
                   e) \
                 (KExpr.app f1 a1) (KExpr.app f2 a2) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "App injectivity (snd): App f1 a1 = App f2 a2 -> a1 = a2. Part of #464.".to_string(),
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
