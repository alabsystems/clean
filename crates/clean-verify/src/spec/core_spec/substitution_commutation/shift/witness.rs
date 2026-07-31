// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Witness-driven successor-shift helper lemmas for substitution commutation.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_substitution_commutation_shift_witness_lemmas(
        &mut self,
    ) -> Result<(), SpecError> {
        // ── Witness-driven equality case: shifting the equality branch by one binder ──
        // Same shape as instantiate_at_bvar_succ_eq_shift, but phrased directly in
        // terms of the paired Nat.sub = 0 witnesses that the generalized nested bvar
        // proof already produces. This avoids forcing a separate idx = depth rewrite.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_succ_eq_from_zero_witnesses".to_string(),
            type_src: concat!(
                "forall (i : Nat) (depth : Nat) (val : KExpr), ",
                "Eq Nat (Nat.sub depth i) Nat.zero -> ",
                "Eq Nat (Nat.sub i depth) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) val (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (depth : Nat) (val : KExpr) ",
                "(h_outer : Eq Nat (Nat.sub depth i) Nat.zero) ",
                "(h_inner : Eq Nat (Nat.sub i depth) Nat.zero) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) val (Nat.succ depth)) ",
                "(lift_at val Nat.zero (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at_bvar_eq_from_zero_witnesses (Nat.succ i) (Nat.succ depth) val ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.succ depth) (Nat.succ i)) ",
                "(Nat.sub depth i) ",
                "Nat.zero ",
                "(nat_sub_succ_succ depth i) ",
                "h_outer) ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.succ i) (Nat.succ depth)) ",
                "(Nat.sub i depth) ",
                "Nat.zero ",
                "(nat_sub_succ_succ i depth) ",
                "h_inner)) ",
                "(Eq.trans KExpr ",
                "(lift_at val Nat.zero (Nat.succ depth)) ",
                "(lift_at (lift_at val Nat.zero depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.symm KExpr ",
                "(lift_at (lift_at val Nat.zero depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at val Nat.zero (Nat.succ depth)) ",
                "(Eq.trans KExpr ",
                "(lift_at (lift_at val Nat.zero depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at val Nat.zero (Nat.add depth (Nat.succ Nat.zero))) ",
                "(lift_at val Nat.zero (Nat.succ depth)) ",
                "(lift_at_compose val Nat.zero depth (Nat.succ Nat.zero)) ",
                "(Eq.cong Nat KExpr ",
                "(fun (amount : Nat) => lift_at val Nat.zero amount) ",
                "(Nat.add depth (Nat.succ Nat.zero)) ",
                "(Nat.succ depth) ",
                "(nat_add_succ_zero depth)))) ",
                "(Eq.symm KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (lift_at val Nat.zero depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at (KExpr.bvar i) val depth) ",
                "(lift_at val Nat.zero depth) ",
                "(instantiate_at_bvar_eq_from_zero_witnesses i depth val h_outer h_inner))))",
            ).to_string()),
            is_axiom: false,
            description: "Witness-driven successor equality shift: if depth and idx are equal via paired Nat.sub zero witnesses, then the succ-depth bvar case is exactly the lift of the depth case. DerivedProved via instantiate_at_bvar_eq_from_zero_witnesses + lift_at_compose. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "lift_at_compose".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Strict-below case: shifting the below branch by one binder ──
        // If idx stays below depth, both sides remain bvars; the shifted theorem
        // packages that the succ-depth/succ-idx below branch matches lifting the
        // depth-level below branch by one binder. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_succ_below_shift".to_string(),
            type_src: concat!(
                "forall (i : Nat) (depth : Nat) (val : KExpr), ",
                "Eq Nat (Nat.sub depth i) ",
                "(Nat.succ (Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) val (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (depth : Nat) (val : KExpr) ",
                "(h_below : Eq Nat (Nat.sub depth i) ",
                "(Nat.succ (Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero)))) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) val (Nat.succ depth)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) val (Nat.succ depth)) ",
                "(instantiate_bvar_at (Nat.succ i) (Nat.succ depth) val) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(instantiate_at_bvar (Nat.succ i) val (Nat.succ depth)) ",
                "(instantiate_bvar_at_below (Nat.succ i) (Nat.succ depth) val ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.succ depth) (Nat.succ i)) ",
                "(Nat.sub depth i) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ depth) (Nat.succ i)) (Nat.succ Nat.zero))) ",
                "(nat_sub_succ_succ depth i) ",
                "(Eq.trans Nat ",
                "(Nat.sub depth i) ",
                "(Nat.succ (Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero))) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ depth) (Nat.succ i)) (Nat.succ Nat.zero))) ",
                "h_below ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                "(Nat.sub depth i) ",
                "(Nat.sub (Nat.succ depth) (Nat.succ i)) ",
                "(Eq.symm Nat ",
                "(Nat.sub (Nat.succ depth) (Nat.succ i)) ",
                "(Nat.sub depth i) ",
                "(nat_sub_succ_succ depth i))))))) ",
                "(Eq.symm KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(Eq.trans KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar i) val depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at (KExpr.bvar i) val depth) ",
                "(KExpr.bvar i) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar i) val depth) ",
                "(instantiate_bvar_at i depth val) ",
                "(KExpr.bvar i) ",
                "(instantiate_at_bvar i val depth) ",
                "(instantiate_bvar_at_below i depth val h_below))) ",
                "(lift_at_bvar_zero_succ i)))",
            ).to_string()),
            is_axiom: false,
            description: "Strict-below successor shift: when idx stays below the cutoff, the succ-depth bvar case is the lifted depth-level below case. DerivedProved via instantiate_bvar_at_below + lift_at_bvar_zero_succ. Part of #464.".to_string(),
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
                "lift_at_bvar_zero_succ".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Above-branch reduction for bvars of the form (succ k) + depth at cutoff depth ──
        // Packages instantiate_at_bvar + instantiate_bvar_at_above + witness
        // construction via nat_sub_zero_add_same_right / nat_sub_pos_add_same_right.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_add_succ_reduces".to_string(),
            type_src: concat!(
                "forall (k : Nat) (depth : Nat) (val : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ k) depth)) val depth) ",
                "(KExpr.bvar (Nat.add k depth))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (k : Nat) (depth : Nat) (val : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ k) depth)) val depth) ",
                "(KExpr.bvar (Nat.sub (Nat.add (Nat.succ k) depth) (Nat.succ Nat.zero))) ",
                "(KExpr.bvar (Nat.add k depth)) ",
                // Step 1: instantiate_at_bvar + instantiate_bvar_at_above
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ k) depth)) val depth) ",
                "(instantiate_bvar_at (Nat.add (Nat.succ k) depth) depth val) ",
                "(KExpr.bvar (Nat.sub (Nat.add (Nat.succ k) depth) (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar (Nat.add (Nat.succ k) depth) val depth) ",
                "(instantiate_bvar_at_above (Nat.add (Nat.succ k) depth) depth val ",
                // h1: sub depth (add (succ k) depth) = 0
                "(Eq.trans Nat ",
                "(Nat.sub depth (Nat.add (Nat.succ k) depth)) ",
                "(Nat.sub (Nat.add Nat.zero depth) (Nat.add (Nat.succ k) depth)) ",
                "Nat.zero ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub x (Nat.add (Nat.succ k) depth)) ",
                "depth ",
                "(Nat.add Nat.zero depth) ",
                "(Eq.symm Nat (Nat.add Nat.zero depth) depth (nat_add_zero depth))) ",
                "(nat_sub_zero_add_same_right Nat.zero (Nat.succ k) depth ",
                "(nat_sub_zero_left (Nat.succ k)))) ",
                // h2: sub (add (succ k) depth) depth = succ(...)
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.add (Nat.succ k) depth) depth) ",
                "(Nat.sub (Nat.add (Nat.succ k) depth) (Nat.add Nat.zero depth)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add (Nat.succ k) depth) depth) (Nat.succ Nat.zero))) ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub (Nat.add (Nat.succ k) depth) x) ",
                "depth ",
                "(Nat.add Nat.zero depth) ",
                "(Eq.symm Nat (Nat.add Nat.zero depth) depth (nat_add_zero depth))) ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.add (Nat.succ k) depth) (Nat.add Nat.zero depth)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add (Nat.succ k) depth) (Nat.add Nat.zero depth)) (Nat.succ Nat.zero))) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add (Nat.succ k) depth) depth) (Nat.succ Nat.zero))) ",
                "(nat_sub_pos_add_same_right (Nat.succ k) Nat.zero depth ",
                "(nat_sub_pos_witness Nat.zero k (nat_sub_zero_left k))) ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.succ (Nat.sub (Nat.sub (Nat.add (Nat.succ k) depth) x) (Nat.succ Nat.zero))) ",
                "(Nat.add Nat.zero depth) ",
                "depth ",
                "(nat_add_zero depth)))))) ",
                // Step 2: bvar(sub ...) = bvar(add k depth) via arithmetic
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.sub (Nat.add (Nat.succ k) depth) (Nat.succ Nat.zero)) ",
                "(Nat.add k depth) ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.add (Nat.succ k) depth) (Nat.succ Nat.zero)) ",
                "(Nat.sub (Nat.succ (Nat.add k depth)) (Nat.succ Nat.zero)) ",
                "(Nat.add k depth) ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                "(Nat.add (Nat.succ k) depth) ",
                "(Nat.succ (Nat.add k depth)) ",
                "(nat_succ_add k depth)) ",
                "(nat_sub_succ_one (Nat.add k depth))))",
            ).to_string()),
            is_axiom: false,
            description: "Above-branch reduction: instantiate_at (bvar (succ k + depth)) val depth = bvar(k + depth). DerivedProved by combining instantiate_at_bvar, instantiate_bvar_at_above with witnesses via nat_sub_zero_add_same_right / nat_sub_pos_add_same_right, and nat_succ_add / nat_sub_succ_one arithmetic. Part of #464.".to_string(),
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
                "nat_add_zero".to_string(),
                "nat_sub_pos_add_same_right".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_add_same_right".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
