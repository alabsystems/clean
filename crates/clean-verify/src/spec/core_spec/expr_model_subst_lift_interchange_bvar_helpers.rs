// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic helpers for the bvar substitution-lift interchange proof.
//!
//! Contains:
//!   - nat_sub_geq_pred_of_pos: if sub(i, d) = succ(k) then sub(d, sub(i, 1)) = 0
//!   - nat_pred_add_right: if sub(i, d) = succ(k) then sub(add(i, sd), 1) = add(sub(i, 1), sd)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_interchange_bvar_helpers(
        &mut self,
    ) -> Result<(), SpecError> {
        // nat_sub_geq_pred_of_pos: if sub(i, d) = succ(k) then sub(d, sub(i, 1)) = 0.
        //
        // Informally: i > d implies d ≤ i - 1.
        //
        // Proof by Nat.rec on i:
        //   i = 0: sub(0, d) = 0 ≠ succ(k), absurd. Discriminator.
        //   i = succ(i'): sub(i, 1) = i' definitionally.
        //     By nat_sub_geq_of_sub_succ(i', d, k, h): sub(d, i') = 0.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_geq_pred_of_pos".to_string(),
            type_src: concat!(
                "forall (d : Nat) (i : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub d (Nat.sub i (Nat.succ Nat.zero))) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) (i : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub i d) (Nat.succ k)) => ",
                    "Nat.rec ",
                    "(fun (i : Nat) => forall (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub d (Nat.sub i (Nat.succ Nat.zero))) Nat.zero) ",
                    "(fun (d : Nat) (k : Nat) ",
                    "(h0 : Eq Nat (Nat.sub Nat.zero d) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub d (Nat.sub Nat.zero (Nat.succ Nat.zero))) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.zero) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero d) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero d) Nat.zero (nat_sub_zero_left d)) ",
                    "h0)) ",
                    "(fun (i' : Nat) ",
                    "(_ : forall (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i' d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub d (Nat.sub i' (Nat.succ Nat.zero))) Nat.zero) ",
                    "(d : Nat) (k : Nat) ",
                    "(hs : Eq Nat (Nat.sub (Nat.succ i') d) (Nat.succ k)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub d (Nat.sub (Nat.succ i') (Nat.succ Nat.zero))) ",
                    "(Nat.sub d i') Nat.zero ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.sub d x) ",
                    "(Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) i' ",
                    "(nat_sub_succ_one i')) ",
                    "(nat_sub_geq_of_sub_succ i' d k hs)) ",
                    "i d k h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(i, d) = succ(k) then sub(d, sub(i, 1)) = 0. ",
                "DerivedProved via Nat.rec on i. Part of #461, #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_geq_of_sub_succ".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_pred_add_right: if sub(i, d) = succ(k) then
        //   sub(add(i, sd), 1) = add(sub(i, 1), sd).
        //
        // Informally: (i + sd) - 1 = (i - 1) + sd when i ≥ 1.
        //
        // Proof by Nat.rec on i:
        //   i = 0: sub(0, d) = 0 ≠ succ(k), absurd. Discriminator.
        //   i = succ(i'): both sides reduce to add(i', sd) definitionally.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_pred_add_right".to_string(),
            type_src: concat!(
                "forall (i : Nat) (sd : Nat) (d : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero)) ",
                "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (sd : Nat) (d : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub i d) (Nat.succ k)) => ",
                    "Nat.rec ",
                    "(fun (i : Nat) => forall (sd : Nat) (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)) ",
                    "(fun (sd : Nat) (d : Nat) (k : Nat) ",
                    "(h0 : Eq Nat (Nat.sub Nat.zero d) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.add Nat.zero sd) (Nat.succ Nat.zero)) ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.add (Nat.sub Nat.zero (Nat.succ Nat.zero)) sd) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero d) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero d) Nat.zero (nat_sub_zero_left d)) ",
                    "h0)) ",
                    "(fun (i' : Nat) ",
                    "(_ : forall (sd : Nat) (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i' d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.add i' sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.sub i' (Nat.succ Nat.zero)) sd)) ",
                    "(sd : Nat) (d : Nat) (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ i') d) (Nat.succ k)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add (Nat.succ i') sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add i' sd) ",
                    "(Nat.add (Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) sd) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add (Nat.succ i') sd) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ (Nat.add i' sd)) (Nat.succ Nat.zero)) ",
                    "(Nat.add i' sd) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.succ i') sd) (Nat.succ (Nat.add i' sd)) ",
                    "(nat_succ_add i' sd)) ",
                    "(nat_sub_succ_one (Nat.add i' sd))) ",
                    "(Eq.symm Nat ",
                    "(Nat.add (Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) sd) ",
                    "(Nat.add i' sd) ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add x sd) ",
                    "(Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) i' ",
                    "(nat_sub_succ_one i')))) ",
                    "i sd d k h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(i, d) = succ(k) then sub(add(i, sd), 1) = add(sub(i, 1), sd). ",
                "DerivedProved via Nat.rec on i. Part of #461, #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::run_with_stack;
    use crate::Specification;

    #[test]
    fn test_interchange_bvar_arith_helpers_are_constructive() {
        let spec = run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        });

        for name in ["nat_sub_geq_pred_of_pos", "nat_pred_add_right"] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("Missing {name}"));
            assert!(def.value_src.is_some(), "{name} should have a proof term");
            assert!(!def.is_axiom, "{name} should not be an axiom");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have no axiom deps: {:?}",
                def.axiom_deps
            );
        }
    }
}
