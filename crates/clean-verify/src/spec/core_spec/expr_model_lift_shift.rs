// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! lift_at shift-by-one transport lemmas split from expr_model_lift_compose.rs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_shift(&mut self) -> Result<(), SpecError> {
        // lift_at_shift_succ_bvar: composing a lift by n at cutoff 0 with a lift
        // by 1 at cutoff d (where d <= n) is the same as a single lift by succ n
        // at cutoff 0. The bvar case of the general lift_at_shift_succ.
        //
        // Proof: rewrite both lifts via lift_at_bvar_geq, then bridge the
        // index arithmetic (j+n)+1 = j+succ(n) via nat_add_succ_zero and
        // nat_add_succ_right. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_shift_succ_bvar".to_string(),
            type_src: concat!(
                "forall (j : Nat) (n : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub d n) Nat.zero -> ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar j) Nat.zero n) d (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar j) Nat.zero (Nat.succ n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (n : Nat) (d : Nat) ",
                    "(h_dn : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) Nat.zero n) d (Nat.succ Nat.zero)) ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.bvar j) Nat.zero (Nat.succ n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) Nat.zero n) d (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar (Nat.add j n)) d (Nat.succ Nat.zero)) ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) (Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x d (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) Nat.zero n) ",
                    "(KExpr.bvar (Nat.add j n)) ",
                    "(lift_at_bvar_geq j Nat.zero n (nat_sub_zero_left j))) ",
                    "(lift_at_bvar_geq (Nat.add j n) d (Nat.succ Nat.zero) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub d (Nat.add j n)) ",
                    "(Nat.sub d (Nat.add n j)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub d x) ",
                    "(Nat.add j n) ",
                    "(Nat.add n j) ",
                    "(nat_add_comm j n)) ",
                    "(nat_sub_zero_add_right d n j h_dn)))) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) (Nat.succ Nat.zero))) ",
                    "(KExpr.bvar (Nat.add j (Nat.succ n))) ",
                    "(lift_at (KExpr.bvar j) Nat.zero (Nat.succ n)) ",
                    "(Eq.cong Nat KExpr KExpr.bvar ",
                    "(Nat.add (Nat.add j n) (Nat.succ Nat.zero)) ",
                    "(Nat.add j (Nat.succ n)) ",
                    "(Eq.trans Nat ",
                    "(Nat.add (Nat.add j n) (Nat.succ Nat.zero)) ",
                    "(Nat.succ (Nat.add j n)) ",
                    "(Nat.add j (Nat.succ n)) ",
                    "(nat_add_succ_zero (Nat.add j n)) ",
                    "(Eq.symm Nat (Nat.add j (Nat.succ n)) (Nat.succ (Nat.add j n)) ",
                    "(nat_add_succ_right j n)))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.bvar j) Nat.zero (Nat.succ n)) ",
                    "(KExpr.bvar (Nat.add j (Nat.succ n))) ",
                    "(lift_at_bvar_geq j Nat.zero (Nat.succ n) (nat_sub_zero_left j))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "BVar case of lift_at_shift_succ: lift(lift(bvar j, 0, n), d, 1) = lift(bvar j, 0, succ n) when d <= n. DerivedProved via lift_at_bvar_geq + nat_add_succ_zero + nat_add_succ_right arithmetic bridge. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_add_comm".to_string(),
                "nat_add_succ_right".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_sub_zero_add_right".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

// Generalized proofs (bvar_gen, gen, shift_succ) are in expr_model_lift_shift_gen.rs.

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn test_lift_shift_bvar_is_tracked() {
        let spec = build_spec_with_stack();

        let bvar = spec
            .definitions()
            .get("lift_at_shift_succ_bvar")
            .expect("lift_at_shift_succ_bvar should exist");
        assert!(bvar.value_src.is_some());
        assert!(!bvar.is_axiom);
        assert_eq!(bvar.proof_status, ProofStatus::DerivedProved);
        assert!(bvar.axiom_deps.is_empty());
    }
}
