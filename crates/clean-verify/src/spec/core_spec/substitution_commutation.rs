// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Substitution commutation lemmas: bvar case chain and nested commutation theorem (PART 11a).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

mod bridge;
mod bridge_cancel;
mod bvar_master;
mod nested;
mod shift;

impl Specification {
    pub(super) fn add_substitution_commutation_lemmas(&mut self) -> Result<(), SpecError> {
        // ── Helper: instantiate_at (bvar 0) val 0 = val ──
        //
        // Chain: instantiate_at_bvar → instantiate_bvar_at_eq → lift_at_amount_zero.
        // Reused by the i=0 and i=1 branches of instantiate_at_bvar_commutes.
        // Part of #461, #464.
        self.add_definition(SpecDefinition {
            name: "instantiate_at_bvar_zero_id".to_string(),
            type_src: "forall (val : KExpr), Eq KExpr (instantiate_at (KExpr.bvar Nat.zero) val Nat.zero) val".to_string(),
            value_src: Some(concat!(
                "fun (val : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar Nat.zero) val Nat.zero) ",
                "(lift_at val Nat.zero Nat.zero) ",
                "val ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar Nat.zero) val Nat.zero) ",
                "(instantiate_bvar_at Nat.zero Nat.zero val) ",
                "(lift_at val Nat.zero Nat.zero) ",
                "(instantiate_at_bvar Nat.zero val Nat.zero) ",
                "(instantiate_bvar_at_eq Nat.zero val)) ",
                "(lift_at_amount_zero val Nat.zero)",
            ).to_string()),
            is_axiom: false,
            description: "instantiate_at (bvar 0) val 0 = val. DerivedProved via bvar unfold + eq case + lift_at_amount_zero. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_eq".to_string(),
                "lift_at_amount_zero".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Case i=0: instantiate_at_bvar_commutes_zero ──
        //
        // LHS: inst(inst(bvar 0, arg, 0), w, 0) = inst(arg, w, 0) via bvar_zero_id.
        // RHS: inst(inst(bvar 0, w, 1), inst(arg,w,0), 0) = inst(bvar 0, inst(arg,w,0), 0)
        //      = inst(arg,w,0) via below case (depth=1 > idx=0) + bvar_zero_id.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_commutes_zero".to_string(),
            type_src: concat!(
                "forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)",
            ).to_string(),
            value_src: Some(concat!(
                "fun (arg : KExpr) (w : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at arg w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                // LHS → instantiate_at arg w 0
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w Nat.zero) ",
                "(instantiate_at (KExpr.bvar Nat.zero) arg Nat.zero) ",
                "arg ",
                "(instantiate_at_bvar_zero_id arg)) ",
                // RHS → instantiate_at arg w 0 (Eq.symm)
                "(Eq.symm KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at arg w Nat.zero) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (KExpr.bvar Nat.zero) (instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at arg w Nat.zero) ",
                // rewrite inst(bvar 0, w, 1) → bvar 0 (below case)
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x (instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(KExpr.bvar Nat.zero) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_bvar_at Nat.zero (Nat.succ Nat.zero) w) ",
                "(KExpr.bvar Nat.zero) ",
                "(instantiate_at_bvar Nat.zero w (Nat.succ Nat.zero)) ",
                // below witness: sub 1 0 = succ(sub(sub 1 0) 1), both = succ 0
                "(instantiate_bvar_at_below Nat.zero (Nat.succ Nat.zero) w ",
                "(Eq.refl Nat (Nat.succ Nat.zero))))) ",
                // inst(bvar 0, inst(arg,w,0), 0) = inst(arg,w,0)
                "(instantiate_at_bvar_zero_id (instantiate_at arg w Nat.zero))))",
            ).to_string()),
            is_axiom: false,
            description: "i=0 case of instantiate_at_bvar_commutes. Both sides reduce to instantiate_at arg w 0. DerivedProved. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at_bvar_zero_id".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Case i=1: instantiate_at_bvar_commutes_one ──
        //
        // LHS: inst(inst(bvar 1, arg, 0), w, 0).
        //   inst(bvar 1, arg, 0) = bvar 0 (above case: idx=1 > depth=0).
        //   Then inst(bvar 0, w, 0) = w via bvar_zero_id.
        // RHS: inst(inst(bvar 1, w, 1), inst(arg,w,0), 0).
        //   inst(bvar 1, w, 1) = lift_at w 0 1 (eq case: idx=depth=1).
        //   Then lift_cancel: inst(lift_at w 0 1, v, 0) = w.
        // Both sides = w.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_commutes_one".to_string(),
            type_src: concat!(
                "forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)",
            ).to_string(),
            value_src: Some(concat!(
                "fun (arg : KExpr) (w : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) w Nat.zero) ",
                "w ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                // ── LHS → w ──
                // inst(bvar 1, arg, 0) → bvar(sub 1 1) = bvar 0 (above case)
                // then inst(bvar 0, w, 0) = w
                "(Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (KExpr.bvar Nat.zero) w Nat.zero) ",
                "w ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) ",
                "(KExpr.bvar Nat.zero) ",
                // chain: inst_at(bvar 1, arg, 0) = bvar(sub 1 1) = bvar 0
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) ",
                "(KExpr.bvar (Nat.sub (Nat.succ Nat.zero) (Nat.succ Nat.zero))) ",
                "(KExpr.bvar Nat.zero) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) arg Nat.zero) ",
                "(instantiate_bvar_at (Nat.succ Nat.zero) Nat.zero arg) ",
                "(KExpr.bvar (Nat.sub (Nat.succ Nat.zero) (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar (Nat.succ Nat.zero) arg Nat.zero) ",
                // above case: h1=sub 0 1=0 (refl), h2=sub 1 0=succ(sub(sub 1 0) 1) (refl)
                "(instantiate_bvar_at_above (Nat.succ Nat.zero) Nat.zero arg ",
                "(Eq.refl Nat Nat.zero) ",
                "(Eq.refl Nat (Nat.succ Nat.zero)))) ",
                // bvar(sub 1 1) = bvar 0 via Eq.cong + nat_sub_succ_one
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.sub (Nat.succ Nat.zero) (Nat.succ Nat.zero)) ",
                "Nat.zero ",
                "(nat_sub_succ_one Nat.zero)))) ",
                // inst(bvar 0, w, 0) = w
                "(instantiate_at_bvar_zero_id w)) ",
                // ── RHS → w (via Eq.symm) ──
                // inst(bvar 1, w, 1) = lift_at w 0 1 (eq case: idx=depth=1)
                // then lift_cancel: inst(lift_at w 0 1, v, 0) = w
                "(Eq.symm KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "w ",
                "(Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (lift_at w Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "w ",
                // rewrite inst(bvar 1, w, 1) → lift_at w 0 1
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x (instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(lift_at w Nat.zero (Nat.succ Nat.zero)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ Nat.zero)) w (Nat.succ Nat.zero)) ",
                "(instantiate_bvar_at (Nat.succ Nat.zero) (Nat.succ Nat.zero) w) ",
                "(lift_at w Nat.zero (Nat.succ Nat.zero)) ",
                "(instantiate_at_bvar (Nat.succ Nat.zero) w (Nat.succ Nat.zero)) ",
                "(instantiate_bvar_at_eq (Nat.succ Nat.zero) w))) ",
                // lift_cancel: inst(lift_at w 0 1, v, 0) = w
                "(lift_cancel w (instantiate_at arg w Nat.zero))))",
            ).to_string()),
            is_axiom: false,
            description: "i=1 case of instantiate_at_bvar_commutes. Both sides reduce to w. LHS via above+bvar_zero_id, RHS via eq case+lift_cancel. DerivedProved. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at_bvar_zero_id".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_bvar_at_eq".to_string(),
                "lift_cancel".to_string(),
                "nat_sub_succ_one".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Above-zero helper: instantiate_at (bvar (j+1)) val 0 = bvar j ──
        // Packages the recurring depth-0 above-case rewrite used by the i>=2 commutation branch. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_succ_zero".to_string(),
            type_src: "forall (j : Nat) (val : KExpr), Eq KExpr (instantiate_at (KExpr.bvar (Nat.succ j)) val Nat.zero) (KExpr.bvar j)".to_string(),
            value_src: Some(concat!(
                "fun (j : Nat) (val : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ j)) val Nat.zero) ",
                "(instantiate_bvar_at (Nat.succ j) Nat.zero val) ",
                "(KExpr.bvar j) ",
                "(instantiate_at_bvar (Nat.succ j) val Nat.zero) ",
                "(Eq.trans KExpr ",
                "(instantiate_bvar_at (Nat.succ j) Nat.zero val) ",
                "(KExpr.bvar (Nat.sub (Nat.succ j) (Nat.succ Nat.zero))) ",
                "(KExpr.bvar j) ",
                "(instantiate_bvar_at_above (Nat.succ j) Nat.zero val ",
                "(nat_sub_zero_left (Nat.succ j)) ",
                "(nat_sub_pos_witness Nat.zero j (nat_sub_zero_left j))) ",
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.sub (Nat.succ j) (Nat.succ Nat.zero)) ",
                "j ",
                "(nat_sub_succ_one j)))",
            ).to_string()),
            is_axiom: false,
            description: "instantiate_at (bvar (j+1)) val 0 = bvar j. DerivedProved via instantiate_bvar_at_above at depth 0. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Above-one helper: instantiate_at (bvar (j+2)) w 1 = bvar (j+1) ──
        // Reconstructs the depth-1 above-case witnesses from nat_sub_succ_succ + nat_sub_zero_left. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_succ_succ_one".to_string(),
            type_src: "forall (j : Nat) (w : KExpr), Eq KExpr (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ j))".to_string(),
            value_src: Some(concat!(
                "fun (j : Nat) (w : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_bvar_at (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero) w) ",
                "(KExpr.bvar (Nat.succ j)) ",
                "(instantiate_at_bvar (Nat.succ (Nat.succ j)) w (Nat.succ Nat.zero)) ",
                "(Eq.trans KExpr ",
                "(instantiate_bvar_at (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero) w) ",
                "(KExpr.bvar (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero))) ",
                "(KExpr.bvar (Nat.succ j)) ",
                "(instantiate_bvar_at_above (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero) w ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.succ Nat.zero) (Nat.succ (Nat.succ j))) ",
                "(Nat.sub Nat.zero (Nat.succ j)) ",
                "Nat.zero ",
                "(nat_sub_succ_succ Nat.zero (Nat.succ j)) ",
                "(nat_sub_zero_left (Nat.succ j))) ",
                "(nat_sub_pos_witness (Nat.succ Nat.zero) (Nat.succ j) ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.succ Nat.zero) (Nat.succ j)) ",
                "(Nat.sub Nat.zero j) ",
                "Nat.zero ",
                "(nat_sub_succ_succ Nat.zero j) ",
                "(nat_sub_zero_left j)))) ",
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero)) ",
                "(Nat.succ j) ",
                "(nat_sub_succ_one (Nat.succ j))))",
            ).to_string()),
            is_axiom: false,
            description: "instantiate_at (bvar (j+2)) w 1 = bvar (j+1). DerivedProved via instantiate_bvar_at_above at depth 1. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_substitution_commutation_shift_lemmas()?;

        // ── Case i>=2: instantiate_at_bvar_commutes_succ_succ ──
        // Both sides reduce to bvar j via the two small above-case helper rewrites. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_commutes_succ_succ".to_string(),
            type_src: concat!(
                "forall (j : Nat) (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (j : Nat) (arg : KExpr) (w : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ j)) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x w Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) arg Nat.zero) ",
                "(KExpr.bvar (Nat.succ j)) ",
                "(instantiate_at_bvar_succ_zero (Nat.succ j) arg)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.succ j)) w Nat.zero) ",
                "(KExpr.bvar j) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at_bvar_succ_zero j w) ",
                "(Eq.symm KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(KExpr.bvar j) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ j)) (instantiate_at arg w Nat.zero) Nat.zero) ",
                "(KExpr.bvar j) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x (instantiate_at arg w Nat.zero) Nat.zero) ",
                "(instantiate_at (KExpr.bvar (Nat.succ (Nat.succ j))) w (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.succ j)) ",
                "(instantiate_at_bvar_succ_succ_one j w)) ",
                "(instantiate_at_bvar_succ_zero j (instantiate_at arg w Nat.zero)))))",
            ).to_string()),
            is_axiom: false,
            description: "i>=2 case of instantiate_at_bvar_commutes. Both sides reduce to the same shifted bvar. DerivedProved. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar_succ_succ_one".to_string(),
                "instantiate_at_bvar_succ_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_bvar_commutes: the bvar case for instantiate_at_zero_commutes
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_commutes".to_string(),
            type_src: "forall (i : Nat) (arg : KExpr) (w : KExpr), Eq KExpr (instantiate_at (instantiate_at (KExpr.bvar i) arg Nat.zero) w Nat.zero) (instantiate_at (instantiate_at (KExpr.bvar i) w (Nat.succ Nat.zero)) (instantiate_at arg w Nat.zero) Nat.zero)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (arg : KExpr) (w : KExpr) => ",
                "Nat.rec ",
                "(fun (n : Nat) => forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar n) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar n) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)) ",
                "(fun (arg : KExpr) (w : KExpr) => instantiate_at_bvar_commutes_zero arg w) ",
                "(fun (j : Nat) (_ : forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar j) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar j) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)) => ",
                "Nat.rec ",
                "(fun (k : Nat) => forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ k)) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ k)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)) ",
                "(fun (arg : KExpr) (w : KExpr) => instantiate_at_bvar_commutes_one arg w) ",
                "(fun (k : Nat) (_ : forall (arg : KExpr) (w : KExpr), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ k)) arg Nat.zero) w Nat.zero) ",
                "(instantiate_at (instantiate_at (KExpr.bvar (Nat.succ k)) w (Nat.succ Nat.zero)) ",
                "(instantiate_at arg w Nat.zero) Nat.zero)) => ",
                "fun (arg : KExpr) (w : KExpr) => instantiate_at_bvar_commutes_succ_succ k arg w) ",
                "j) ",
                "i arg w",
            ).to_string()),
            is_axiom: false,
            description: "BVar case of instantiate_at_zero_commutes. DerivedProved by Nat.rec splitting into the i=0, i=1, and i>=2 branches. Part of #661, #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "instantiate_at_bvar_commutes_one".to_string(),
                "instantiate_at_bvar_commutes_succ_succ".to_string(),
                "instantiate_at_bvar_commutes_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "instantiate_at_nested_commutes_goal".to_string(),
            type_src: "KExpr -> Prop".to_string(),
            value_src: Some(concat!(
                "fun (body : KExpr) => ",
                "forall (arg : KExpr) (w : KExpr) (subst_depth : Nat) (outer_depth : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (instantiate_at body arg subst_depth) w (Nat.add subst_depth outer_depth)) ",
                "(instantiate_at (instantiate_at body w (Nat.succ (Nat.add subst_depth outer_depth))) ",
                "(instantiate_at arg w outer_depth) subst_depth)"
            ).to_string()),
            is_axiom: false,
            description: "Reducible motive alias for binder-aware nested substitution commutation. Keeps the KExpr.rec target reducible during declaration checking. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq".to_string(),
                "KExpr".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // bridge_cancel registers `inst_overlift_cancel`, which the nested
        // above-case (equal sub-branch) consumes. Register it before the nested
        // helpers so the dependency is available at declaration-check time.
        self.add_substitution_commutation_bridge_cancel_lemmas()?;
        self.add_nested_commutation_bvar_helpers()?;
        self.add_substitution_commutation_bridge_lemmas()?;
        self.add_substitution_commutation_bvar_master()?;

        Ok(())
    }
}
