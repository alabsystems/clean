// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic lemma and substitution structural proof terms for the kernel
//! ProofLibrary.
//!
//! Covers DerivedProved definitions from:
//! - foundation_types.rs: Bool/Nat operations (nat_add_zero, nat_sub_self, etc.)
//! - foundation_arith_lemmas.rs: Basic Nat arithmetic (add/sub properties)
//! - foundation_arith_positivity.rs: Nat positivity witnesses
//! - foundation_arith_transport.rs: Nat arithmetic transport lemmas
//! - foundation_arith_witnesses.rs: Nat sub witnesses
//! - expr_model.rs: instantiate_at_bvar, instantiate_bvar_at variants
//! - expr_model_lift_cancel.rs: lift_cancel_gen
//! - expr_model_lift_compose.rs: lift_at_compose
//! - expr_model_lift_shift*.rs: lift_at_shift_succ variants
//! - expr_model_subst_lift_*.rs: subst/lift interchange
//! - substitution_commutation*.rs: instantiate_at_bvar_commutes variants
//! - substitution_def_eq.rs: instantiate_at_*_preserves_def_eq
//! - reduction_witnesses.rs: delta/iota type/def_eq preservation
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_arith_subst_proofs(&mut self) {
        // === foundation_types.rs ===

        // `Bool.and`/`Bool.or`/`Bool.not` are no longer foundation SpecDefinitions:
        // the foundation now registers the kernel `Bool` surface via
        // `env.init_bool()` (so the BoolAnalysis corpus reduces against the kernel
        // recursor), which provides these as kernel-verified `Bool.rec`-based
        // reducing definitions. They are therefore not self-verification
        // properties and carry no ProofLibrary entry here.

        self.proofs.insert(
            "nat_add_zero".to_string(),
            ProofTerm::new(
                "nat_add_zero",
                "nat_add_zero",
                "Nat.add 0 0 = 0 (DerivedProved via Eq.refl)",
            ),
        );

        self.proofs.insert(
            "nat_sub_self".to_string(),
            ProofTerm::new(
                "nat_sub_self",
                "nat_sub_self",
                "Nat.sub n n = 0 (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_sub_succ_succ".to_string(),
            ProofTerm::new(
                "nat_sub_succ_succ",
                "nat_sub_succ_succ",
                "Nat.sub (succ a) (succ b) = Nat.sub a b (DerivedProved via Eq.refl)",
            ),
        );

        // === foundation_arith_lemmas.rs ===

        self.proofs.insert(
            "nat_sub_zero_right".to_string(),
            ProofTerm::new(
                "nat_sub_zero_right",
                "nat_sub_zero_right",
                "Nat.sub n 0 = n (DerivedProved via Eq.refl on concrete zero)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_left".to_string(),
            ProofTerm::new(
                "nat_sub_zero_left",
                "nat_sub_zero_left",
                "Nat.sub 0 n = 0 for all n (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_add_succ_zero".to_string(),
            ProofTerm::new(
                "nat_add_succ_zero",
                "nat_add_succ_zero",
                "Nat.add n 1 = Nat.succ n (DerivedProved via Eq.refl + structural registration)",
            ),
        );

        self.proofs.insert(
            "nat_add_zero_right".to_string(),
            ProofTerm::new(
                "nat_add_zero_right",
                "nat_add_zero_right",
                "Nat.add n 0 = n (DerivedProved via Eq.refl on concrete zero branch)",
            ),
        );

        self.proofs.insert(
            "nat_zero_add".to_string(),
            ProofTerm::new(
                "nat_zero_add",
                "nat_zero_add",
                "Nat.add 0 n = n (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_succ_add".to_string(),
            ProofTerm::new(
                "nat_succ_add",
                "nat_succ_add",
                "Nat.add (succ a) b = succ (Nat.add a b) (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_add_succ_right".to_string(),
            ProofTerm::new(
                "nat_add_succ_right",
                "nat_add_succ_right",
                "Nat.add a (succ b) = succ (Nat.add a b) (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_add_comm".to_string(),
            ProofTerm::new(
                "nat_add_comm",
                "nat_add_comm",
                "Nat.add a b = Nat.add b a (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "nat_add_succ_zero_is_succ_pred".to_string(),
            ProofTerm::new(
                "nat_add_succ_zero_is_succ_pred",
                "nat_add_succ_zero_is_succ_pred",
                "add(n, 1) = succ(pred(add(n, 1))) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_succ_one".to_string(),
            ProofTerm::new(
                "nat_sub_succ_one",
                "nat_sub_succ_one",
                "sub(succ(n), 1) = n (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_add_succ_zero_one".to_string(),
            ProofTerm::new(
                "nat_sub_add_succ_zero_one",
                "nat_sub_add_succ_zero_one",
                "sub(add(n, 1), 1) = n (DerivedProved via transport chain)",
            ),
        );

        // === foundation_arith_positivity.rs ===

        self.proofs.insert(
            "nat_pos_witness_from_succ_eq".to_string(),
            ProofTerm::new(
                "nat_pos_witness_from_succ_eq",
                "nat_pos_witness_from_succ_eq",
                "If sub(a, b) = succ(k) then positivity witness (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_pos_add_right".to_string(),
            ProofTerm::new(
                "nat_sub_pos_add_right",
                "nat_sub_pos_add_right",
                "If sub(a, b) > 0 then sub(a+c, b) > 0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_pos_succ".to_string(),
            ProofTerm::new(
                "nat_sub_pos_succ",
                "nat_sub_pos_succ",
                "If sub(a, b) = succ(k) then sub(succ(a), succ(b)) = succ(k) (DerivedProved)",
            ),
        );

        // === foundation_arith_transport.rs ===

        self.proofs.insert(
            "nat_sub_pos_add_same_right".to_string(),
            ProofTerm::new(
                "nat_sub_pos_add_same_right",
                "nat_sub_pos_add_same_right",
                "sub(a+c, b) positivity from sub(a,b) positivity (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_add_monotone".to_string(),
            ProofTerm::new(
                "nat_sub_zero_add_monotone",
                "nat_sub_zero_add_monotone",
                "If sub(a,b)=0 then sub(a,b+c)=0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_add_same_right".to_string(),
            ProofTerm::new(
                "nat_sub_zero_add_same_right",
                "nat_sub_zero_add_same_right",
                "sub(a+c, b+c) = sub(a, b) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_succ_gap_to_add".to_string(),
            ProofTerm::new(
                "nat_sub_zero_succ_gap_to_add",
                "nat_sub_zero_succ_gap_to_add",
                "If sub(a,b)=0 and sub(b,a)=succ(k) then b=a+succ(k) (DerivedProved)",
            ),
        );

        // === foundation_arith_witnesses.rs ===

        self.proofs.insert(
            "nat_sub_pos_witness".to_string(),
            ProofTerm::new(
                "nat_sub_pos_witness",
                "nat_sub_pos_witness",
                "Nat sub positivity witness extraction (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_implies_sub_succ_zero".to_string(),
            ProofTerm::new(
                "nat_sub_zero_implies_sub_succ_zero",
                "nat_sub_zero_implies_sub_succ_zero",
                "If sub(a,b)=0 then sub(succ(a),b)<=1 (DerivedProved)",
            ),
        );

        // === expr_model.rs: instantiate bvar helpers ===

        self.proofs.insert(
            "instantiate_at_bvar".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar",
                "instantiate_at_bvar",
                "Unfolding: instantiate_at (bvar i) val depth = instantiate_bvar_at i depth val (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_bvar_at_below".to_string(),
            ProofTerm::new(
                "instantiate_bvar_at_below",
                "instantiate_bvar_at_below",
                "If idx < depth, instantiate_bvar_at returns bvar idx unchanged (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "instantiate_bvar_at_eq".to_string(),
            ProofTerm::new(
                "instantiate_bvar_at_eq",
                "instantiate_bvar_at_eq",
                "If idx == depth, instantiate_bvar_at substitutes with lifted val (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_bvar_at_eq_from_zero_witnesses".to_string(),
            ProofTerm::new(
                "instantiate_bvar_at_eq_from_zero_witnesses",
                "instantiate_bvar_at_eq_from_zero_witnesses",
                "Witness-driven equality branch for instantiate_bvar_at (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_eq_from_zero_witnesses",
                "instantiate_at_bvar_eq_from_zero_witnesses",
                "Witness-driven equality branch for instantiate_at on bvars (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_bvar_at_above".to_string(),
            ProofTerm::new(
                "instantiate_bvar_at_above",
                "instantiate_bvar_at_above",
                "If idx > depth, instantiate_bvar_at decrements the index (DerivedProved)",
            ),
        );

        // === expr_model_lift_cancel.rs ===

        self.proofs.insert(
            "lift_cancel_gen_bvar".to_string(),
            ProofTerm::new(
                "lift_cancel_gen_bvar",
                "lift_cancel_gen_bvar",
                "lift_cancel_gen bvar case via Nat.rec convoy on sub cutoff idx (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_cancel_gen".to_string(),
            ProofTerm::new(
                "lift_cancel_gen",
                "lift_cancel_gen",
                "Generalized lift_cancel at arbitrary cutoff (DerivedProved via cutoff-universalized KExpr.rec)",
            ),
        );

        // === expr_model_lift_compose.rs ===

        self.proofs.insert(
            "nat_add_assoc".to_string(),
            ProofTerm::new(
                "nat_add_assoc",
                "nat_add_assoc",
                "(a + b) + c = a + (b + c) (DerivedProved via Nat.rec on third addend)",
            ),
        );

        self.proofs.insert(
            "nat_sub_zero_add_right".to_string(),
            ProofTerm::new(
                "nat_sub_zero_add_right",
                "nat_sub_zero_add_right",
                "If cutoff <= idx then cutoff <= idx + amount (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "lift_at_compose_bvar".to_string(),
            ProofTerm::new(
                "lift_at_compose_bvar",
                "lift_at_compose_bvar",
                "Composing two lifts at same cutoff on bvar equals one lift by summed amount (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_at_compose".to_string(),
            ProofTerm::new(
                "lift_at_compose",
                "lift_at_compose",
                "Composing two lifts at same cutoff equals one lift by summed amount (DerivedProved via KExpr.rec)",
            ),
        );

        // === expr_model_lift_shift*.rs ===

        self.proofs.insert(
            "lift_at_shift_succ_bvar".to_string(),
            ProofTerm::new(
                "lift_at_shift_succ_bvar",
                "lift_at_shift_succ_bvar",
                "BVar case of lift_at_shift_succ (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_at_shift_succ_bvar_gen".to_string(),
            ProofTerm::new(
                "lift_at_shift_succ_bvar_gen",
                "lift_at_shift_succ_bvar_gen",
                "Generalized bvar case of lift_at_shift_succ at arbitrary cutoff (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_at_shift_succ_gen".to_string(),
            ProofTerm::new(
                "lift_at_shift_succ_gen",
                "lift_at_shift_succ_gen",
                "lift(lift(e, c, n), add(c,d), 1) = lift(e, c, succ n) when d <= n (DerivedProved via KExpr.rec)",
            ),
        );

        self.proofs.insert(
            "lift_at_shift_succ".to_string(),
            ProofTerm::new(
                "lift_at_shift_succ",
                "lift_at_shift_succ",
                "lift(lift(e, 0, n), d, 1) = lift(e, 0, succ n) when d <= n (DerivedProved)",
            ),
        );

        // === expr_model_subst_lift_cross_*.rs ===

        self.proofs.insert(
            "nat_sub_zero_trans".to_string(),
            ProofTerm::new(
                "nat_sub_zero_trans",
                "nat_sub_zero_trans",
                "Transitivity of <= via Nat.sub: sub(a,b)=0 and sub(b,c)=0 -> sub(a,c)=0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_at_cross_compose_bvar".to_string(),
            ProofTerm::new(
                "lift_at_cross_compose_bvar",
                "lift_at_cross_compose_bvar",
                "Cross-cutoff lift composition for bvars (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lift_at_cross_compose".to_string(),
            ProofTerm::new(
                "lift_at_cross_compose",
                "lift_at_cross_compose",
                "Cross-cutoff lift composition (DerivedProved via KExpr.rec)",
            ),
        );

        // === expr_model_subst_lift_interchange*.rs ===

        self.proofs.insert(
            "nat_sub_geq_of_sub_succ".to_string(),
            ProofTerm::new(
                "nat_sub_geq_of_sub_succ",
                "nat_sub_geq_of_sub_succ",
                "If sub(succ(a), b) = succ(k) then sub(b, a) = 0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_bvar_below".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_bvar_below",
                "subst_lift_interchange_bvar_below",
                "Subst-lift interchange bvar below case (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_bvar_between".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_bvar_between",
                "subst_lift_interchange_bvar_between",
                "Subst-lift interchange bvar between case (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_bvar_gen".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_bvar_gen",
                "subst_lift_interchange_bvar_gen",
                "Generalized bvar case of subst/lift interchange at arbitrary cutoff (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_bvar_equal".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_bvar_equal",
                "subst_lift_interchange_bvar_equal",
                "Subst-lift interchange bvar equal case (i = c+od) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_bvar_above".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_bvar_above",
                "subst_lift_interchange_bvar_above",
                "Subst-lift interchange bvar above case (i > c+od) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_sub_geq_pred_of_pos".to_string(),
            ProofTerm::new(
                "nat_sub_geq_pred_of_pos",
                "nat_sub_geq_pred_of_pos",
                "If sub(i, d) = succ(k) then sub(d, sub(i, 1)) = 0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "nat_pred_add_right".to_string(),
            ProofTerm::new(
                "nat_pred_add_right",
                "nat_pred_add_right",
                "If sub(i, d) = succ(k) then sub(add(i, sd), 1) = add(sub(i, 1), sd) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "subst_lift_interchange_gen".to_string(),
            ProofTerm::new(
                "subst_lift_interchange_gen",
                "subst_lift_interchange_gen",
                "Generalized subst/lift interchange at arbitrary cutoff (DerivedProved via KExpr.rec)",
            ),
        );

        // === substitution_commutation*.rs ===

        self.proofs.insert(
            "instantiate_at_bvar_commutes".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_commutes",
                "instantiate_at_bvar_commutes",
                "BVar case of instantiate_at_nested_commutes (DerivedProved via Nat.rec convoy)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_commutes_one".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_commutes_one",
                "instantiate_at_bvar_commutes_one",
                "BVar commutation at depth 1 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_commutes_succ_succ".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_commutes_succ_succ",
                "instantiate_at_bvar_commutes_succ_succ",
                "BVar commutation at succ-succ (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_commutes_zero".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_commutes_zero",
                "instantiate_at_bvar_commutes_zero",
                "BVar commutation at depth 0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_succ_succ_one".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_succ_succ_one",
                "instantiate_at_bvar_succ_succ_one",
                "BVar substitution succ-succ-one case (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_succ_zero".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_succ_zero",
                "instantiate_at_bvar_succ_zero",
                "BVar substitution succ-zero case (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_bvar_zero_id".to_string(),
            ProofTerm::new(
                "instantiate_at_bvar_zero_id",
                "instantiate_at_bvar_zero_id",
                "BVar substitution zero-identity case (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_nested_commutes_goal".to_string(),
            ProofTerm::new(
                "instantiate_at_nested_commutes_goal",
                "instantiate_at_nested_commutes_goal",
                "Motive alias for nested instantiate commutation (DerivedProved)",
            ),
        );

        // === substitution_commutation_nested.rs ===

        self.proofs.insert(
            "instantiate_app_lam_eq".to_string(),
            ProofTerm::new(
                "instantiate_app_lam_eq",
                "instantiate_app_lam_eq",
                "instantiate (app (lam A b) a) val = app (lam ...) ... (DerivedProved via Eq chain)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_nested_commutes".to_string(),
            ProofTerm::new(
                "instantiate_at_nested_commutes",
                "instantiate_at_nested_commutes",
                "Nested instantiate_at commutation (DerivedProved via KExpr.rec)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_zero_commutes".to_string(),
            ProofTerm::new(
                "instantiate_at_zero_commutes",
                "instantiate_at_zero_commutes",
                "instantiate_at commutation at depth 0 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_nested_commutes_zero_subst".to_string(),
            ProofTerm::new(
                "instantiate_nested_commutes_zero_subst",
                "instantiate_nested_commutes_zero_subst",
                "Nested instantiate commutation at depth 0 substitution (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "instantiate_subst_commutes_eq".to_string(),
            ProofTerm::new(
                "instantiate_subst_commutes_eq",
                "instantiate_subst_commutes_eq",
                "Substitution commutation equality (DerivedProved)",
            ),
        );

        // === substitution_def_eq.rs: DefEq preservation under substitution ===

        self.proofs.insert(
            "instantiate_at_app_preserves_def_eq".to_string(),
            ProofTerm::new(
                "instantiate_at_app_preserves_def_eq",
                "instantiate_at_app_preserves_def_eq",
                "instantiate_at preserves application DefEq (DerivedProved via instantiate_at_app + DefEq.app_cong + Eq.subst)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_lam_preserves_def_eq".to_string(),
            ProofTerm::new(
                "instantiate_at_lam_preserves_def_eq",
                "instantiate_at_lam_preserves_def_eq",
                "instantiate_at preserves lam DefEq (DerivedProved via instantiate_at_lam + DefEq.lam_cong + Eq.subst)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_pi_preserves_def_eq".to_string(),
            ProofTerm::new(
                "instantiate_at_pi_preserves_def_eq",
                "instantiate_at_pi_preserves_def_eq",
                "instantiate_at preserves pi DefEq (DerivedProved via instantiate_at_pi + DefEq.pi_cong + Eq.subst)",
            ),
        );

        // === reduction_witnesses.rs: delta/iota preservation ===

        self.proofs.insert(
            "delta_subst_preserves_def_eq_at".to_string(),
            ProofTerm::new(
                "delta_subst_preserves_def_eq_at",
                "delta_subst_preserves_def_eq_at",
                "Delta substitution preserves DefEq at given depth (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "delta_type_preservation_fwd".to_string(),
            ProofTerm::new(
                "delta_type_preservation_fwd",
                "delta_type_preservation_fwd",
                "Delta reduction preserves typing (forward) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "delta_type_preservation_bwd".to_string(),
            ProofTerm::new(
                "delta_type_preservation_bwd",
                "delta_type_preservation_bwd",
                "Delta reduction preserves typing (backward) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "iota_subst_preserves_def_eq_at".to_string(),
            ProofTerm::new(
                "iota_subst_preserves_def_eq_at",
                "iota_subst_preserves_def_eq_at",
                "Iota substitution preserves DefEq at given depth (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "iota_type_preservation_fwd".to_string(),
            ProofTerm::new(
                "iota_type_preservation_fwd",
                "iota_type_preservation_fwd",
                "Iota reduction preserves typing (forward) (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "iota_type_preservation_bwd".to_string(),
            ProofTerm::new(
                "iota_type_preservation_bwd",
                "iota_type_preservation_bwd",
                "Iota reduction preserves typing (backward) (DerivedProved)",
            ),
        );
    }
}
