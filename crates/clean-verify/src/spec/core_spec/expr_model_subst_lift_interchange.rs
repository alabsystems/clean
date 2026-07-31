// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Substitution-lift interchange proofs (cutoff-generalized).
//!
//! Contains:
//!   - nat_sub_geq_of_sub_succ: succ(a) > b implies a ≥ b
//!   - subst_lift_interchange_bvar_gen: generalized bvar case at arbitrary cutoff (DerivedProved)
//!   - subst_lift_interchange_gen: full KExpr.rec proof at arbitrary cutoff (DerivedProved)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_interchange(&mut self) -> Result<(), SpecError> {
        // nat_sub_geq_of_sub_succ: if sub(succ(a), b) = succ(k), then sub(b, a) = 0.
        //
        // Informally: succ(a) > b implies a ≥ b (i.e., b ≤ a).
        //
        // Proof by double Nat.rec on b (outer) and a (inner):
        //   b = 0: sub(0, a) = 0 by nat_sub_zero_left.
        //   b = succ(b'):
        //     a = 0: sub(succ(0), succ(b')) = sub(0, b') = 0, contradicts succ(k).
        //     a = succ(a'): sub(succ(succ(a')), succ(b')) = sub(succ(a'), b') = succ(k).
        //       By IH: sub(b', a') = 0.
        //       Then sub(succ(b'), succ(a')) = sub(b', a') = 0.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_geq_of_sub_succ".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub (Nat.succ a) b) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub b a) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub (Nat.succ a) b) (Nat.succ k)) => ",
                    "Nat.rec ",
                    // motive: universalize a, k
                    "(fun (b : Nat) => forall (a : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub (Nat.succ a) b) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub b a) Nat.zero) ",
                    // b = 0: sub(0, a) = 0
                    "(fun (a : Nat) (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ a) Nat.zero) (Nat.succ k)) => ",
                    "nat_sub_zero_left a) ",
                    // b = succ(b')
                    "(fun (b' : Nat) ",
                    "(ih : forall (a : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub (Nat.succ a) b') (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub b' a) Nat.zero) ",
                    "(a : Nat) (k : Nat) ",
                    "(h_s : Eq Nat (Nat.sub (Nat.succ a) (Nat.succ b')) (Nat.succ k)) => ",
                    // inner Nat.rec on a
                    "Nat.rec ",
                    "(fun (a : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ a) (Nat.succ b')) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.succ b') a) Nat.zero) ",
                    // a = 0: contradiction from sub(1, succ(b')) = sub(0, b') = 0
                    "(fun (h_z : Eq Nat (Nat.sub (Nat.succ Nat.zero) (Nat.succ b')) ",
                    "(Nat.succ k)) => ",
                    "Eq.symm Nat Nat.zero (Nat.sub (Nat.succ b') Nat.zero) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.sub (Nat.succ b') Nat.zero) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ b')) ",
                    "(Nat.succ k) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ b')) ",
                    "Nat.zero ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ b')) ",
                    "(Nat.sub Nat.zero b') ",
                    "Nat.zero ",
                    "(nat_sub_succ_succ Nat.zero b') ",
                    "(nat_sub_zero_left b'))) ",
                    "h_z))) ",
                    // a = succ(a')
                    "(fun (a' : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ a') (Nat.succ b')) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.succ b') a') Nat.zero) ",
                    "(h_ss : Eq Nat (Nat.sub (Nat.succ (Nat.succ a')) (Nat.succ b')) ",
                    "(Nat.succ k)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ b') (Nat.succ a')) ",
                    "(Nat.sub b' a') ",
                    "Nat.zero ",
                    "(nat_sub_succ_succ b' a') ",
                    "(ih a' k ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ a') b') ",
                    "(Nat.sub (Nat.succ (Nat.succ a')) (Nat.succ b')) ",
                    "(Nat.succ k) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ (Nat.succ a')) (Nat.succ b')) ",
                    "(Nat.sub (Nat.succ a') b') ",
                    "(nat_sub_succ_succ (Nat.succ a') b')) ",
                    "h_ss))) ",
                    "a h_s) ",
                    "b a k h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(succ(a), b) = succ(k) then sub(b, a) = 0. ",
                "Informally: succ(a) > b implies a >= b. ",
                "DerivedProved via double Nat.rec (on b, a) with nat_sub_succ_succ + discriminator. ",
                "Part of #461, #464.",
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
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subst_lift_interchange_bvar_below: j < c case. Both sides = bvar j.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange_bvar_below".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c : Nat) (sd : Nat) (d : Nat) (w : KExpr) ",
                "(k : Nat) (k3 : Nat), ",
                "Eq Nat (Nat.sub d j) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub c j) (Nat.succ k3) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (c : Nat) (sd : Nat) (d : Nat) (w : KExpr) ",
                    "(k : Nat) (k3 : Nat) ",
                    "(h_dj : Eq Nat (Nat.sub d j) (Nat.succ k)) ",
                    "(h_cj : Eq Nat (Nat.sub c j) (Nat.succ k3)) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                    "(KExpr.bvar j) ",
                    "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                    "(instantiate_at (KExpr.bvar j) w (Nat.add d sd)) ",
                    "(KExpr.bvar j) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w (Nat.add d sd)) ",
                    "(lift_at (KExpr.bvar j) c sd) (KExpr.bvar j) ",
                    "(lift_at_bvar_below j c sd ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c j) k3 h_cj))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar j) w (Nat.add d sd)) ",
                    "(instantiate_bvar_at j (Nat.add d sd) w) ",
                    "(KExpr.bvar j) ",
                    "(instantiate_at_bvar j w (Nat.add d sd)) ",
                    "(instantiate_bvar_at_below j (Nat.add d sd) w ",
                    "(nat_sub_pos_add_right d sd j ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub d j) k h_dj))))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                    "(KExpr.bvar j) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                    "(lift_at (KExpr.bvar j) c sd) ",
                    "(KExpr.bvar j) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x c sd) ",
                    "(instantiate_at (KExpr.bvar j) w d) (KExpr.bvar j) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar j) w d) ",
                    "(instantiate_bvar_at j d w) ",
                    "(KExpr.bvar j) ",
                    "(instantiate_at_bvar j w d) ",
                    "(instantiate_bvar_at_below j d w ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub d j) k h_dj)))) ",
                    "(lift_at_bvar_below j c sd ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c j) k3 h_cj))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Subst-lift interchange bvar below case. Both sides = bvar j. Part of #461, #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "lift_at_bvar_below".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subst_lift_interchange_bvar_between: c <= j < d case. Both sides = bvar(add(j,sd)).
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange_bvar_between".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c : Nat) (sd : Nat) (d : Nat) (w : KExpr) ",
                "(k : Nat), ",
                "Eq Nat (Nat.sub d j) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub c j) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd)",
            ).to_string(),
            value_src: Some(concat!(
                "fun (j : Nat) (c : Nat) (sd : Nat) (d : Nat) (w : KExpr) ",
                "(k : Nat) ",
                "(h_dj : Eq Nat (Nat.sub d j) (Nat.succ k)) ",
                "(h_cj : Eq Nat (Nat.sub c j) Nat.zero) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                "(KExpr.bvar (Nat.add j sd)) ",
                "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar j) c sd) w (Nat.add d sd)) ",
                "(instantiate_at (KExpr.bvar (Nat.add j sd)) w (Nat.add d sd)) ",
                "(KExpr.bvar (Nat.add j sd)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.add d sd)) ",
                "(lift_at (KExpr.bvar j) c sd) (KExpr.bvar (Nat.add j sd)) ",
                "(lift_at_bvar_geq j c sd h_cj)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add j sd)) w (Nat.add d sd)) ",
                "(instantiate_bvar_at (Nat.add j sd) (Nat.add d sd) w) ",
                "(KExpr.bvar (Nat.add j sd)) ",
                "(instantiate_at_bvar (Nat.add j sd) w (Nat.add d sd)) ",
                "(instantiate_bvar_at_below (Nat.add j sd) (Nat.add d sd) w ",
                "(nat_sub_pos_add_same_right d j sd ",
                "(nat_pos_witness_from_succ_eq (Nat.sub d j) k h_dj))))) ",
                "(Eq.symm KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                "(KExpr.bvar (Nat.add j sd)) ",
                "(Eq.trans KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar j) w d) c sd) ",
                "(lift_at (KExpr.bvar j) c sd) ",
                "(KExpr.bvar (Nat.add j sd)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x c sd) ",
                "(instantiate_at (KExpr.bvar j) w d) (KExpr.bvar j) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar j) w d) ",
                "(instantiate_bvar_at j d w) ",
                "(KExpr.bvar j) ",
                "(instantiate_at_bvar j w d) ",
                "(instantiate_bvar_at_below j d w ",
                "(nat_pos_witness_from_succ_eq (Nat.sub d j) k h_dj)))) ",
                "(lift_at_bvar_geq j c sd h_cj)))",
            ).to_string()),
            is_axiom: false,
            description: "Subst-lift interchange bvar between case. Both sides = bvar(add(j,sd)). Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(), "Eq.symm".to_string(), "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(), "instantiate_bvar_at_below".to_string(),
                "lift_at_bvar_geq".to_string(), "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_same_right".to_string(),
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
    fn test_interchange_bvar_helpers_are_constructive() {
        let spec = run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        });

        for name in [
            "nat_sub_geq_of_sub_succ",
            "subst_lift_interchange_bvar_below",
            "subst_lift_interchange_bvar_between",
        ] {
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
                "{name} should have no remaining helper blockers: {:?}",
                def.axiom_deps
            );
        }
    }
}
