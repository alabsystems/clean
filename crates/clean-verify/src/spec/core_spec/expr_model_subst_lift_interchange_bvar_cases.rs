// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Equal and above bvar sub-cases for substitution-lift interchange.
//!
//! Contains:
//!   - subst_lift_interchange_bvar_equal: equal case (i = c+od)
//!   - subst_lift_interchange_bvar_above: above case (i > c+od)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_interchange_bvar_cases(
        &mut self,
    ) -> Result<(), SpecError> {
        // subst_lift_interchange_bvar_equal: i = c+od case.
        //
        // When sub(c, i) = 0, sub(add(c, od), i) = 0, sub(i, add(c, od)) = 0:
        // LHS reduces to lift_at(w, 0, add(sd, add(c, od))) via lift_at_bvar_geq +
        //   instantiate_at_bvar_eq_from_zero_witnesses (with nat_add_comm transport).
        // RHS reduces to lift_at(lift_at(w, 0, add(c, od)), c, sd) via
        //   instantiate_at_bvar_eq_from_zero_witnesses + Eq.cong.
        // Bridge: lift_at_cross_compose + nat_add_comm.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange_bvar_equal".to_string(),
            type_src: concat!(
                "forall (i : Nat) (c : Nat) (sd : Nat) (od : Nat) (w : KExpr), ",
                "Eq Nat (Nat.sub c i) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.add c od) i) Nat.zero -> ",
                "Eq Nat (Nat.sub i (Nat.add c od)) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                "(Nat.add sd (Nat.add c od))) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (c : Nat) (sd : Nat) (od : Nat) (w : KExpr) ",
                    "(h_ci : Eq Nat (Nat.sub c i) Nat.zero) ",
                    "(h_codi : Eq Nat (Nat.sub (Nat.add c od) i) Nat.zero) ",
                    "(h_icod : Eq Nat (Nat.sub i (Nat.add c od)) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(lift_at w Nat.zero (Nat.add sd (Nat.add c od))) ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(instantiate_at (KExpr.bvar (Nat.add i sd)) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(lift_at w Nat.zero (Nat.add sd (Nat.add c od))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(lift_at (KExpr.bvar i) c sd) (KExpr.bvar (Nat.add i sd)) ",
                    "(lift_at_bvar_geq i c sd h_ci)) ",
                    "(instantiate_at_bvar_eq_from_zero_witnesses ",
                    "(Nat.add i sd) (Nat.add sd (Nat.add c od)) w ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add sd (Nat.add c od)) (Nat.add i sd)) ",
                    "(Nat.sub (Nat.add (Nat.add c od) sd) (Nat.add i sd)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.add i sd)) ",
                    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od))) ",
                    "(nat_sub_zero_add_same_right (Nat.add c od) i sd h_codi)) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add i sd) (Nat.add sd (Nat.add c od))) ",
                    "(Nat.sub (Nat.add i sd) (Nat.add (Nat.add c od) sd)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub (Nat.add i sd) x) ",
                    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od))) ",
                    "(nat_sub_zero_add_same_right i (Nat.add c od) sd h_icod)))) ",
                    "(Eq.trans KExpr ",
                    "(lift_at w Nat.zero (Nat.add sd (Nat.add c od))) ",
                    "(lift_at w Nat.zero (Nat.add (Nat.add c od) sd)) ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at w Nat.zero x) ",
                    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od))) ",
                    "(Eq.trans KExpr ",
                    "(lift_at w Nat.zero (Nat.add (Nat.add c od) sd)) ",
                    "(lift_at (lift_at w Nat.zero (Nat.add c od)) c sd) ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(Eq.trans KExpr ",
                    "(lift_at w Nat.zero (Nat.add (Nat.add c od) sd)) ",
                    "(lift_at (lift_at w Nat.zero (Nat.add c od)) ",
                    "(Nat.add Nat.zero c) sd) ",
                    "(lift_at (lift_at w Nat.zero (Nat.add c od)) c sd) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (lift_at w Nat.zero (Nat.add c od)) ",
                    "(Nat.add Nat.zero c) sd) ",
                    "(lift_at w Nat.zero (Nat.add (Nat.add c od) sd)) ",
                    "(lift_at_cross_compose w Nat.zero (Nat.add c od) c sd ",
                    "(nat_sub_zero_add_right c c od (nat_sub_self c)))) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at (lift_at w Nat.zero ",
                    "(Nat.add c od)) x sd) ",
                    "(Nat.add Nat.zero c) c ",
                    "(nat_zero_add c))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x c sd) ",
                    "(lift_at w Nat.zero (Nat.add c od)) ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add c od)) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add c od)) ",
                    "(lift_at w Nat.zero (Nat.add c od)) ",
                    "(instantiate_at_bvar_eq_from_zero_witnesses i ",
                    "(Nat.add c od) w h_codi h_icod)))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Subst-lift interchange bvar equal case (i = c+od). ",
                "DerivedProved. Part of #461, #464.",
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
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "lift_at_bvar_geq".to_string(),
                "lift_at_cross_compose".to_string(),
                "nat_add_comm".to_string(),
                "nat_sub_self".to_string(),
                "nat_sub_zero_add_right".to_string(),
                "nat_sub_zero_add_same_right".to_string(),
                "nat_zero_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subst_lift_interchange_bvar_above: i > c+od case.
        //
        // LHS reduces to bvar(sub(add(i, sd), 1)), RHS to bvar(add(sub(i, 1), sd)).
        // Bridge: nat_pred_add_right.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange_bvar_above".to_string(),
            type_src: concat!(
                "forall (i : Nat) (c : Nat) (sd : Nat) (od : Nat) (w : KExpr) ",
                "(k : Nat), ",
                "Eq Nat (Nat.sub c i) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.add c od) i) Nat.zero -> ",
                "Eq Nat (Nat.sub i (Nat.add c od)) (Nat.succ k) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                "(Nat.add sd (Nat.add c od))) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (c : Nat) (sd : Nat) (od : Nat) (w : KExpr) ",
                    "(k : Nat) ",
                    "(h_ci : Eq Nat (Nat.sub c i) Nat.zero) ",
                    "(h_codi : Eq Nat (Nat.sub (Nat.add c od) i) Nat.zero) ",
                    "(h_icod : Eq Nat (Nat.sub i (Nat.add c od)) (Nat.succ k)) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(KExpr.bvar (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero))) ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(instantiate_at (KExpr.bvar (Nat.add i sd)) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(KExpr.bvar (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(lift_at (KExpr.bvar i) c sd) (KExpr.bvar (Nat.add i sd)) ",
                    "(lift_at_bvar_geq i c sd h_ci)) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar (Nat.add i sd)) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(instantiate_bvar_at (Nat.add i sd) ",
                    "(Nat.add sd (Nat.add c od)) w) ",
                    "(KExpr.bvar (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero))) ",
                    "(instantiate_at_bvar (Nat.add i sd) w ",
                    "(Nat.add sd (Nat.add c od))) ",
                    "(instantiate_bvar_at_above (Nat.add i sd) ",
                    "(Nat.add sd (Nat.add c od)) w ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add sd (Nat.add c od)) (Nat.add i sd)) ",
                    "(Nat.sub (Nat.add (Nat.add c od) sd) (Nat.add i sd)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.add i sd)) ",
                    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od))) ",
                    "(nat_sub_zero_add_same_right (Nat.add c od) i sd h_codi)) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add i sd) (Nat.add sd (Nat.add c od))) ",
                    "(Nat.sub (Nat.add i sd) (Nat.add (Nat.add c od) sd)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add i sd) ",
                    "(Nat.add sd (Nat.add c od))) (Nat.succ Nat.zero))) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub (Nat.add i sd) x) ",
                    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od))) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add i sd) (Nat.add (Nat.add c od) sd)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add i sd) ",
                    "(Nat.add (Nat.add c od) sd)) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add i sd) ",
                    "(Nat.add sd (Nat.add c od))) (Nat.succ Nat.zero))) ",
                    "(nat_sub_pos_add_same_right i (Nat.add c od) sd ",
                    "(nat_pos_witness_from_succ_eq ",
                    "(Nat.sub i (Nat.add c od)) k h_icod)) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (z : Nat) => Nat.succ (Nat.sub z (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.add i sd) (Nat.add (Nat.add c od) sd)) ",
                    "(Nat.sub (Nat.add i sd) (Nat.add sd (Nat.add c od))) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub (Nat.add i sd) x) ",
                    "(Nat.add (Nat.add c od) sd) (Nat.add sd (Nat.add c od)) ",
                    "(Eq.symm Nat (Nat.add sd (Nat.add c od)) ",
                    "(Nat.add (Nat.add c od) sd) ",
                    "(nat_add_comm sd (Nat.add c od)))))))))) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.bvar (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero))) ",
                    "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)) ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(Eq.cong Nat KExpr KExpr.bvar ",
                    "(Nat.sub (Nat.add i sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd) ",
                    "(nat_pred_add_right i sd (Nat.add c od) k h_icod)) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd) ",
                    "(lift_at (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) c sd) ",
                    "(KExpr.bvar (Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x c sd) ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add c od)) ",
                    "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.bvar i) w (Nat.add c od)) ",
                    "(instantiate_bvar_at i (Nat.add c od) w) ",
                    "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                    "(instantiate_at_bvar i w (Nat.add c od)) ",
                    "(instantiate_bvar_at_above i (Nat.add c od) w ",
                    "h_codi ",
                    "(nat_pos_witness_from_succ_eq ",
                    "(Nat.sub i (Nat.add c od)) k h_icod)))) ",
                    "(lift_at_bvar_geq (Nat.sub i (Nat.succ Nat.zero)) c sd ",
                    "(nat_sub_zero_trans c (Nat.add c od) ",
                    "(Nat.sub i (Nat.succ Nat.zero)) ",
                    "(nat_sub_zero_add_right c c od (nat_sub_self c)) ",
                    "(nat_sub_geq_pred_of_pos (Nat.add c od) i k h_icod))))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Subst-lift interchange bvar above case (i > c+od). ",
                "Bridge via nat_pred_add_right. DerivedProved. Part of #461, #464.",
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
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_add_comm".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_pred_add_right".to_string(),
                "nat_sub_geq_pred_of_pos".to_string(),
                "nat_sub_pos_add_same_right".to_string(),
                "nat_sub_self".to_string(),
                "nat_sub_zero_add_right".to_string(),
                "nat_sub_zero_add_same_right".to_string(),
                "nat_sub_zero_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;

    #[test]
    fn test_interchange_bvar_equal_above_are_constructive() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();

        for name in [
            "subst_lift_interchange_bvar_equal",
            "subst_lift_interchange_bvar_above",
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
                "{name} should have no axiom deps: {:?}",
                def.axiom_deps
            );
        }
    }
}
