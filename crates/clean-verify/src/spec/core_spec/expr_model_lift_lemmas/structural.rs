// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_structural_lemmas(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // lift_at structural lemmas (#663)
        // =========================================================

        // lift_at_sort: lift_at on sort is identity
        self.add_definition(SpecDefinition {
            name: "lift_at_sort".to_string(),
            type_src: "forall (n : Level) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.sort n) cutoff amount) (KExpr.sort n)".to_string(),
            value_src: Some("fun (n : Level) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.sort n)".to_string()),
            is_axiom: false,
            description: "lift_at (sort n) cutoff amount = sort n.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "lift_at_const".to_string(),
            type_src: "forall (n : Name) (us : ListType Level) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.const n us) cutoff amount) (KExpr.const n us)".to_string(),
            value_src: Some(
                "fun (n : Name) (us : ListType Level) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.const n us)".to_string(),
            ),
            is_axiom: false,
            description: "lift_at (const n us) cutoff amount = const n us.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_app — DerivedProved via Eq.refl. This stays on the normal
        // checked path: lift_at unfolds to the generated KExpr.rec, and iota
        // reduction on the KExpr.app constructor exposes this match arm.
        self.add_definition(SpecDefinition {
            name: "lift_at_app".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.app f a) cutoff amount) (KExpr.app (lift_at f cutoff amount) (lift_at a cutoff amount))".to_string(),
            value_src: Some("fun (f : KExpr) (a : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.app (lift_at f cutoff amount) (lift_at a cutoff amount))".to_string()),
            is_axiom: false,
            description: "lift_at distributes over app. DerivedProved via Eq.refl through checked KExpr.rec iota reduction. Part of #663, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_lam — DerivedProved via Eq.refl + structural registration.
        // Same iota false negative bypass as lift_at_app. Part of #663, #461.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_lam".to_string(),
            type_src: "forall (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.lam ty body) cutoff amount) (KExpr.lam (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string(),
            value_src: Some("fun (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.lam (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string()),
            is_axiom: false,
            description: "lift_at distributes over lam (incrementing cutoff). DerivedProved via Eq.refl + structural registration. Part of #663, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_pi — DerivedProved via Eq.refl + structural registration.
        // Same iota false negative bypass as lift_at_app. Part of #663, #461.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_pi".to_string(),
            type_src: "forall (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.pi ty body) cutoff amount) (KExpr.pi (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string(),
            value_src: Some("fun (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.pi (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string()),
            is_axiom: false,
            description: "lift_at distributes over pi (incrementing cutoff). DerivedProved via Eq.refl + structural registration. Part of #663, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_let_ — the let_ analogue of lift_at_lam: ty and val at the
        // current cutoff, body at succ cutoff. DerivedProved via Eq.refl +
        // structural registration (same iota false negative bypass). Part of
        // the let-promotion surgery (task #28).
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_let_".to_string(),
            type_src: "forall (ty : KExpr) (v : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (KExpr.let_ ty v body) cutoff amount) (KExpr.let_ (lift_at ty cutoff amount) (lift_at v cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string(),
            value_src: Some("fun (ty : KExpr) (v : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.let_ (lift_at ty cutoff amount) (lift_at v cutoff amount) (lift_at body (Nat.succ cutoff) amount))".to_string()),
            is_axiom: false,
            description: "lift_at distributes over let_ (ty/val at cutoff, body at succ cutoff). DerivedProved via Eq.refl + structural registration. Part of the let-promotion surgery (task #28).".to_string(),
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
mod tests {
    use super::*;
    use clean_kernel::Name;

    #[test]
    fn lift_at_app_checked_registration_succeeds_on_kexpr_rec_iota() {
        let mut spec = Specification::new_empty();
        spec.add_foundation_types().unwrap();
        spec.add_foundation_arith_lemmas().unwrap();
        spec.add_foundation_arith_witnesses().unwrap();
        spec.add_foundation_arith_positivity().unwrap();
        spec.add_foundation_arith_transport().unwrap();
        spec.add_expr_model().unwrap();

        spec.add_expr_model_lift_structural_lemmas()
            .expect("lift_at_app should register through checked KExpr.rec iota");
        assert!(
            spec.env()
                .get_const(&Name::from_string("lift_at_app"))
                .is_some(),
            "lift_at_app should be inserted by normal checked registration"
        );
    }
}
