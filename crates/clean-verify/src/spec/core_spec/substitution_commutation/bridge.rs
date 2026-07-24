// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BVar-specialized lift/substitution bridge lemmas.
//!
//! These are the cutoff-0 bridge fragments needed before the fully generic
//! equal-case proof can be lifted through `KExpr.rec`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_substitution_commutation_bridge_lemmas(&mut self) -> Result<(), SpecError> {
        // ── One-step bridge on bvars ──
        // After lifting a bvar by one at cutoff 0, substituting at succ depth is
        // the same as substituting at depth first and then lifting the result by
        // one. The proof splits on i vs depth using the witness-driven shift
        // helpers from shift.rs and the Nat.add decomposition witness for the
        // strict-above branch. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_lift_at_zero_succ_commutes_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (w : KExpr) (depth : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (w : KExpr) (depth : Nat) => ",
                "Nat.rec ",
                "(fun (outer : Nat) => ",
                "Eq Nat (Nat.sub depth i) outer -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero))) ",
                // outer = 0
                "(fun (h_outer : Eq Nat (Nat.sub depth i) Nat.zero) => ",
                "Nat.rec ",
                "(fun (inner : Nat) => ",
                "Eq Nat (Nat.sub i depth) inner -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero))) ",
                // equal branch
                "(fun (h_inner : Eq Nat (Nat.sub i depth) Nat.zero) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.succ depth)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(lift_at_bvar_zero_succ i)) ",
                "(instantiate_at_bvar_succ_eq_from_zero_witnesses i depth w h_outer h_inner)) ",
                // strict-above branch
                "(fun (gap : Nat) ",
                "(_ : Eq Nat (Nat.sub i depth) gap -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero))) ",
                "(h_gap : Eq Nat (Nat.sub i depth) (Nat.succ gap)) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ (Nat.succ gap)) depth)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) w (Nat.succ depth)) ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ (Nat.succ gap)) depth)) w (Nat.succ depth)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.succ depth)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(lift_at_bvar_zero_succ i)) ",
                "(Eq.cong Nat KExpr ",
                "(fun (idx : Nat) => instantiate_at (KExpr.bvar idx) w (Nat.succ depth)) ",
                "(Nat.succ i) ",
                "(Nat.add (Nat.succ (Nat.succ gap)) depth) ",
                "(Eq.trans Nat ",
                "(Nat.succ i) ",
                "(Nat.succ (Nat.add (Nat.succ gap) depth)) ",
                "(Nat.add (Nat.succ (Nat.succ gap)) depth) ",
                "(Eq.cong Nat Nat Nat.succ ",
                "i ",
                "(Nat.add (Nat.succ gap) depth) ",
                "(nat_sub_zero_succ_gap_to_add i depth gap h_outer h_gap)) ",
                "(Eq.symm Nat ",
                "(Nat.add (Nat.succ (Nat.succ gap)) depth) ",
                "(Nat.succ (Nat.add (Nat.succ gap) depth)) ",
                "(nat_succ_add (Nat.succ gap) depth))))) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ (Nat.succ gap)) depth)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar (Nat.add (Nat.succ gap) depth)) w depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at_bvar_succ_gap_shift depth (Nat.succ gap) w) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at (KExpr.bvar (Nat.add (Nat.succ gap) depth)) w depth) ",
                "(instantiate_at (KExpr.bvar i) w depth) ",
                "(Eq.cong Nat KExpr ",
                "(fun (idx : Nat) => instantiate_at (KExpr.bvar idx) w depth) ",
                "(Nat.add (Nat.succ gap) depth) ",
                "i ",
                "(Eq.symm Nat ",
                "i ",
                "(Nat.add (Nat.succ gap) depth) ",
                "(nat_sub_zero_succ_gap_to_add i depth gap h_outer h_gap)))))) ",
                "(Nat.sub i depth) ",
                "(Eq.refl Nat (Nat.sub i depth))) ",
                // strict-below branch
                "(fun (k : Nat) ",
                "(_ : Eq Nat (Nat.sub depth i) k -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero))) ",
                "(h_below_raw : Eq Nat (Nat.sub depth i) (Nat.succ k)) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ depth)) ",
                "(instantiate_at (KExpr.bvar (Nat.succ i)) w (Nat.succ depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w depth) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.succ depth)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ i)) ",
                "(lift_at_bvar_zero_succ i)) ",
                "(instantiate_at_bvar_succ_below_shift i depth w ",
                "(Eq.trans Nat ",
                "(Nat.sub depth i) ",
                "(Nat.succ k) ",
                "(Nat.succ (Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero))) ",
                "h_below_raw ",
                "(Eq.cong Nat Nat Nat.succ ",
                "k ",
                "(Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero)) ",
                "(Eq.symm Nat ",
                "(Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero)) ",
                "k ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.sub depth i) (Nat.succ Nat.zero)) ",
                "(Nat.sub (Nat.succ k) (Nat.succ Nat.zero)) ",
                "k ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                "(Nat.sub depth i) ",
                "(Nat.succ k) ",
                "h_below_raw) ",
                "(nat_sub_succ_one k))))))) ",
                "(Nat.sub depth i) ",
                "(Eq.refl Nat (Nat.sub depth i))",
            ).to_string()),
            is_axiom: false,
            description: "BVar one-step lift/substitution bridge at cutoff 0. DerivedProved by splitting on i vs depth and routing the three branches through the constructive successor-shift helpers. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_bvar_succ_below_shift".to_string(),
                "instantiate_at_bvar_succ_eq_from_zero_witnesses".to_string(),
                "instantiate_at_bvar_succ_gap_shift".to_string(),
                "lift_at_bvar_zero_succ".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_succ_gap_to_add".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Arbitrary cutoff-0 bridge on bvars ──
        // This is the bvar-only version of the equal-case substitution/lift
        // interchange theorem. The step case peels one unit of lifting, rewrites
        // the intermediate lifted bvar with lift_at_bvar_geq, applies the
        // one-step bridge, then folds the remaining lift stack back together with
        // lift_at_compose. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_lift_at_zero_commutes_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero subst_depth) w (Nat.add subst_depth outer_depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero subst_depth)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat) => ",
                "Nat.rec ",
                "(fun (sd : Nat) => ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero sd) w (Nat.add sd outer_depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero sd)) ",
                // sd = 0
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero Nat.zero) w (Nat.add Nat.zero outer_depth)) ",
                "(instantiate_at (KExpr.bvar i) w outer_depth) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero Nat.zero) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero Nat.zero) w (Nat.add Nat.zero outer_depth)) ",
                "(instantiate_at (KExpr.bvar i) w (Nat.add Nat.zero outer_depth)) ",
                "(instantiate_at (KExpr.bvar i) w outer_depth) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.add Nat.zero outer_depth)) ",
                "(lift_at (KExpr.bvar i) Nat.zero Nat.zero) ",
                "(KExpr.bvar i) ",
                "(lift_at_amount_zero (KExpr.bvar i) Nat.zero)) ",
                "(Eq.cong Nat KExpr ",
                "(fun (d : Nat) => instantiate_at (KExpr.bvar i) w d) ",
                "(Nat.add Nat.zero outer_depth) ",
                "outer_depth ",
                "(nat_zero_add outer_depth))) ",
                "(Eq.symm KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero Nat.zero) ",
                "(instantiate_at (KExpr.bvar i) w outer_depth) ",
                "(lift_at_amount_zero (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero))) ",
                // sd = succ d
                "(fun (d : Nat) ",
                "(ih : Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero d) w (Nat.add d outer_depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero d)) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) w (Nat.add (Nat.succ d) outer_depth)) ",
                "(instantiate_at (lift_at (KExpr.bvar (Nat.add i d)) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ (Nat.add d outer_depth))) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.succ d)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) w (Nat.add (Nat.succ d) outer_depth)) ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) w (Nat.succ (Nat.add d outer_depth))) ",
                "(instantiate_at (lift_at (KExpr.bvar (Nat.add i d)) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ (Nat.add d outer_depth))) ",
                "(Eq.cong Nat KExpr ",
                "(fun (depth : Nat) => instantiate_at (lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) w depth) ",
                "(Nat.add (Nat.succ d) outer_depth) ",
                "(Nat.succ (Nat.add d outer_depth)) ",
                "(nat_succ_add d outer_depth)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.succ (Nat.add d outer_depth))) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) ",
                "(lift_at (KExpr.bvar (Nat.add i d)) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) ",
                "(lift_at (lift_at (KExpr.bvar i) Nat.zero d) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar (Nat.add i d)) Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.symm KExpr ",
                "(lift_at (lift_at (KExpr.bvar i) Nat.zero d) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) ",
                "(Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.bvar i) Nat.zero d) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.add d (Nat.succ Nat.zero))) ",
                "(lift_at (KExpr.bvar i) Nat.zero (Nat.succ d)) ",
                "(lift_at_compose_bvar i Nat.zero d (Nat.succ Nat.zero)) ",
                "(Eq.cong Nat KExpr ",
                "(fun (amount : Nat) => lift_at (KExpr.bvar i) Nat.zero amount) ",
                "(Nat.add d (Nat.succ Nat.zero)) ",
                "(Nat.succ d) ",
                "(nat_add_succ_zero d)))) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar i) Nat.zero d) ",
                "(KExpr.bvar (Nat.add i d)) ",
                "(lift_at_bvar_geq i Nat.zero d (nat_sub_zero_left i)))))) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar (Nat.add i d)) Nat.zero (Nat.succ Nat.zero)) w (Nat.succ (Nat.add d outer_depth))) ",
                "(lift_at (instantiate_at (KExpr.bvar (Nat.add i d)) w (Nat.add d outer_depth)) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.succ d)) ",
                "(instantiate_at_lift_at_zero_succ_commutes_bvar (Nat.add i d) w (Nat.add d outer_depth)) ",
                "(Eq.trans KExpr ",
                "(lift_at (instantiate_at (KExpr.bvar (Nat.add i d)) w (Nat.add d outer_depth)) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (lift_at (KExpr.bvar i) Nat.zero d) w (Nat.add d outer_depth)) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.succ d)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at (KExpr.bvar (Nat.add i d)) w (Nat.add d outer_depth)) ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero d) w (Nat.add d outer_depth)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w (Nat.add d outer_depth)) ",
                "(KExpr.bvar (Nat.add i d)) ",
                "(lift_at (KExpr.bvar i) Nat.zero d) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.bvar i) Nat.zero d) ",
                "(KExpr.bvar (Nat.add i d)) ",
                "(lift_at_bvar_geq i Nat.zero d (nat_sub_zero_left i))))) ",
                "(Eq.trans KExpr ",
                "(lift_at (instantiate_at (lift_at (KExpr.bvar i) Nat.zero d) w (Nat.add d outer_depth)) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero d) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.succ d)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at (lift_at (KExpr.bvar i) Nat.zero d) w (Nat.add d outer_depth)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero d) ",
                "ih) ",
                "(Eq.trans KExpr ",
                "(lift_at (lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero d) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.add d (Nat.succ Nat.zero))) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero (Nat.succ d)) ",
                "(lift_at_compose (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero d (Nat.succ Nat.zero)) ",
                "(Eq.cong Nat KExpr ",
                "(fun (amount : Nat) => lift_at (instantiate_at (KExpr.bvar i) w outer_depth) Nat.zero amount) ",
                "(Nat.add d (Nat.succ Nat.zero)) ",
                "(Nat.succ d) ",
                "(nat_add_succ_zero d))))))) ",
                "subst_depth",
            ).to_string()),
            is_axiom: false,
            description: "BVar cutoff-0 substitution/lift interchange for arbitrary lift amount. DerivedProved by Nat.rec on subst_depth, peeling one unit of lift through the constructive one-step bvar bridge. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_lift_at_zero_succ_commutes_bvar".to_string(),
                "lift_at_amount_zero".to_string(),
                "lift_at_bvar_geq".to_string(),
                "lift_at_compose".to_string(),
                "lift_at_compose_bvar".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_zero_add".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Substitution/lift interchange (cutoff-zero, full KExpr) ──
        //
        // The standard de Bruijn substitution lemma:
        //   inst(lift_at e 0 sd, w, sd+od) = lift_at(inst(e, w, od), 0, sd)
        //
        // DerivedProved from subst_lift_interchange_gen at c=0 with
        // nat_zero_add transport on both sides:
        //   add(sd, od) = add(sd, add(0, od))  and  add(0, od) = od
        //
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (lift_at e Nat.zero subst_depth) w ",
                "(Nat.add subst_depth outer_depth)) ",
                "(lift_at (instantiate_at e w outer_depth) Nat.zero subst_depth)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at e Nat.zero subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (lift_at e Nat.zero subst_depth) w ",
                    "(Nat.add subst_depth (Nat.add Nat.zero outer_depth))) ",
                    "(lift_at (instantiate_at e w outer_depth) Nat.zero subst_depth) ",
                    // transport: add(sd, od) → add(sd, add(0, od))
                    "(Eq.cong Nat KExpr ",
                    "(fun (d : Nat) => instantiate_at (lift_at e Nat.zero subst_depth) w d) ",
                    "(Nat.add subst_depth outer_depth) ",
                    "(Nat.add subst_depth (Nat.add Nat.zero outer_depth)) ",
                    "(Eq.symm Nat ",
                    "(Nat.add subst_depth (Nat.add Nat.zero outer_depth)) ",
                    "(Nat.add subst_depth outer_depth) ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add subst_depth x) ",
                    "(Nat.add Nat.zero outer_depth) outer_depth ",
                    "(nat_zero_add outer_depth)))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (lift_at e Nat.zero subst_depth) w ",
                    "(Nat.add subst_depth (Nat.add Nat.zero outer_depth))) ",
                    "(lift_at (instantiate_at e w (Nat.add Nat.zero outer_depth)) ",
                    "Nat.zero subst_depth) ",
                    "(lift_at (instantiate_at e w outer_depth) Nat.zero subst_depth) ",
                    // apply gen at c=0
                    "(subst_lift_interchange_gen e w Nat.zero subst_depth outer_depth) ",
                    // transport: add(0, od) → od in RHS
                    "(Eq.cong Nat KExpr ",
                    "(fun (d : Nat) => lift_at (instantiate_at e w d) Nat.zero subst_depth) ",
                    "(Nat.add Nat.zero outer_depth) outer_depth ",
                    "(nat_zero_add outer_depth)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Substitution/lift interchange at cutoff zero: ",
                "inst(lift_at(e, 0, sd), w, sd+od) = lift_at(inst(e, w, od), 0, sd). ",
                "DerivedProved from subst_lift_interchange_gen at c=0 with nat_zero_add transport. ",
                "No remaining axiom deps (full interchange chain is DerivedProved). Part of #461, #464.",
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
                "nat_zero_add".to_string(),
                "subst_lift_interchange_gen".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Equal case bridge: i = subst_depth ──
        //
        // Combines the equal_lhs reduction, the subst_lift_interchange axiom,
        // and Eq.symm of equal_rhs to derive the full equal case of the
        // nested bvar commutation:
        //
        //   LHS = inst(lift_at arg 0 sd, w, sd+od)   [by equal_lhs]
        //       = lift_at(inst(arg, w, od), 0, sd)    [by interchange]
        //       = RHS                                  [by Eq.symm equal_rhs]
        //
        // DerivedProved modulo the subst_lift_interchange axiom.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_nested_commutes_bvar_equal".to_string(),
            type_src: concat!(
                "forall (i : Nat) (arg : KExpr) (w : KExpr) ",
                "(subst_depth : Nat) (outer_depth : Nat), ",
                "Eq Nat (Nat.sub subst_depth i) Nat.zero -> ",
                "Eq Nat (Nat.sub i subst_depth) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                "(Nat.add subst_depth outer_depth)) ",
                "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                "(instantiate_at arg w outer_depth) subst_depth)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (arg : KExpr) (w : KExpr) ",
                    "(subst_depth : Nat) (outer_depth : Nat) ",
                    "(h_outer : Eq Nat (Nat.sub subst_depth i) Nat.zero) ",
                    "(h_inner : Eq Nat (Nat.sub i subst_depth) Nat.zero) => ",
                    // Eq.trans: LHS → interchange midpoint → RHS
                    "Eq.trans KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) arg subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (lift_at arg Nat.zero subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    // step 1: equal_lhs rewrites inner substitution to lift
                    "(instantiate_at_nested_commutes_bvar_equal_lhs i arg w ",
                    "subst_depth outer_depth h_outer h_inner) ",
                    // step 2: interchange → Eq.symm(equal_rhs)
                    "(Eq.trans KExpr ",
                    "(instantiate_at (lift_at arg Nat.zero subst_depth) w ",
                    "(Nat.add subst_depth outer_depth)) ",
                    "(lift_at (instantiate_at arg w outer_depth) Nat.zero subst_depth) ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(subst_lift_interchange arg w subst_depth outer_depth) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate_at (KExpr.bvar i) w ",
                    "(Nat.succ (Nat.add subst_depth outer_depth))) ",
                    "(instantiate_at arg w outer_depth) subst_depth) ",
                    "(lift_at (instantiate_at arg w outer_depth) Nat.zero subst_depth) ",
                    "(instantiate_at_nested_commutes_bvar_equal_rhs i arg w ",
                    "subst_depth outer_depth h_outer h_inner)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Equal case (i = subst_depth) of nested substitution commutation on bvars. ",
                "Chains equal_lhs, subst_lift_interchange, and Eq.symm(equal_rhs). ",
                "DerivedProved modulo subst_lift_interchange. Part of #461, #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_nested_commutes_bvar_equal_lhs".to_string(),
                "instantiate_at_nested_commutes_bvar_equal_rhs".to_string(),
                "subst_lift_interchange".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
