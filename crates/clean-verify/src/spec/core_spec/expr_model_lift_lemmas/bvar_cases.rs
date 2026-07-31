// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_bvar_lemmas(&mut self) -> Result<(), SpecError> {
        // lift_at_bvar_below: derived proof for i < cutoff case.
        //
        // Proof strategy: same Eq.cong + Nat.rec iota as instantiate_bvar_at_below.
        // The hypothesis h gives Nat.sub cutoff i = Nat.succ k.
        // Eq.cong maps h through the Nat.rec in lift_bvar_at's definition.
        // Nat.rec on Nat.succ iota+beta-reduces to KExpr.bvar i.
        // The elaborator delta-unfolds lift_at (KExpr.bvar i) to lift_bvar_at.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_bvar_below".to_string(),
            type_src: "forall (i : Nat) (cutoff : Nat) (amount : Nat), Eq Nat (Nat.sub cutoff i) (Nat.succ (Nat.sub (Nat.sub cutoff i) (Nat.succ Nat.zero))) -> Eq KExpr (lift_at (KExpr.bvar i) cutoff amount) (KExpr.bvar i)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (cutoff : Nat) (amount : Nat) ",
                "(h : Eq Nat (Nat.sub cutoff i) (Nat.succ (Nat.sub (Nat.sub cutoff i) (Nat.succ Nat.zero)))) => ",
                "Eq.cong Nat KExpr ",
                "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => KExpr) ",
                "(KExpr.bvar (Nat.add i amount)) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n) ",
                "(Nat.sub cutoff i) ",
                "(Nat.succ (Nat.sub (Nat.sub cutoff i) (Nat.succ Nat.zero))) ",
                "h",
            ).to_string()),
            is_axiom: false,
            description: "If i < cutoff, lift_at doesn't change bvar i. DerivedProved via Eq.cong + Nat.rec iota. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_bvar_geq: derived proof for i >= cutoff case.
        //
        // Proof strategy: hypothesis h gives Nat.sub cutoff i = Nat.zero.
        // Eq.cong maps h through the Nat.rec in lift_bvar_at's definition.
        // Nat.rec on Nat.zero reduces to KExpr.bvar (Nat.add i amount).
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_bvar_geq".to_string(),
            type_src: "forall (i : Nat) (cutoff : Nat) (amount : Nat), Eq Nat (Nat.sub cutoff i) Nat.zero -> Eq KExpr (lift_at (KExpr.bvar i) cutoff amount) (KExpr.bvar (Nat.add i amount))".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (cutoff : Nat) (amount : Nat) ",
                "(h : Eq Nat (Nat.sub cutoff i) Nat.zero) => ",
                "Eq.cong Nat KExpr ",
                "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => KExpr) ",
                "(KExpr.bvar (Nat.add i amount)) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n) ",
                "(Nat.sub cutoff i) ",
                "Nat.zero ",
                "h",
            ).to_string()),
            is_axiom: false,
            description: "If i >= cutoff, lift_at adds amount. DerivedProved via Eq.cong + Nat.rec iota. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_rec_const: Nat.rec with constant zero/succ cases always returns
        // the constant value. This belongs after KExpr is introduced because
        // its motive and result type mention KExpr directly. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_rec_const".to_string(),
            type_src: "forall (v : KExpr) (n : Nat), Eq KExpr (Nat.rec (fun (_ : Nat) => KExpr) v (fun (_ : Nat) (_ : KExpr) => v) n) v".to_string(),
            value_src: Some(concat!(
                "fun (v : KExpr) (n : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq KExpr (Nat.rec (fun (_ : Nat) => KExpr) v (fun (_ : Nat) (_ : KExpr) => v) k) v) ",
                "(Eq.refl KExpr v) ",
                "(fun (k : Nat) (ih : Eq KExpr (Nat.rec (fun (_ : Nat) => KExpr) v (fun (_ : Nat) (_ : KExpr) => v) k) v) => ",
                "Eq.refl KExpr v) ",
                "n",
            ).to_string()),
            is_axiom: false,
            description: "Nat.rec with constant branches always returns the constant. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_bvar_at_amount_zero: derived proof that lifting by 0 is identity.
        //
        // Proof strategy: lift_bvar_at idx cutoff 0 delta-unfolds to
        // Nat.rec motive (KExpr.bvar (Nat.add idx 0)) (fun _ _ => KExpr.bvar idx) (Nat.sub cutoff idx)
        // Since Nat.add idx 0 reduces to idx by definition, both branches
        // return KExpr.bvar idx, so nat_rec_const applies directly.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_bvar_at_amount_zero".to_string(),
            type_src: "forall (idx : Nat) (cutoff : Nat), Eq KExpr (lift_bvar_at idx cutoff Nat.zero) (KExpr.bvar idx)".to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (cutoff : Nat) => ",
                "nat_rec_const (KExpr.bvar idx) (Nat.sub cutoff idx)",
            ).to_string()),
            is_axiom: false,
            description: "Lifting a bvar by amount 0 is identity. DerivedProved via nat_rec_const. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["nat_rec_const".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_cancel_gen_bvar_below: generalized lift_cancel on a bvar below cutoff.
        //
        // Proof strategy: rewrite the lifted bvar back to `bvar idx` with
        // lift_at_bvar_below, unfold instantiate_at's bvar case, then reuse
        // instantiate_bvar_at_below with the same witness.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_cancel_gen_bvar_below".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (val : KExpr) (cutoff : Nat), ",
                "Eq Nat (Nat.sub cutoff idx) (Nat.succ (Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) val cutoff) ",
                "(KExpr.bvar idx)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (val : KExpr) (cutoff : Nat) ",
                "(h : Eq Nat (Nat.sub cutoff idx) (Nat.succ (Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero)))) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) val cutoff) ",
                "(instantiate_at (KExpr.bvar idx) val cutoff) ",
                "(KExpr.bvar idx) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x val cutoff) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) ",
                "(KExpr.bvar idx) ",
                "(lift_at_bvar_below idx cutoff (Nat.succ Nat.zero) h)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar idx) val cutoff) ",
                "(instantiate_bvar_at idx cutoff val) ",
                "(KExpr.bvar idx) ",
                "(instantiate_at_bvar idx val cutoff) ",
                "(instantiate_bvar_at_below idx cutoff val h))",
            )
            .to_string()),
            is_axiom: false,
            description: "Generalized lift_cancel bvar branch when idx < cutoff. DerivedProved via lift_at_bvar_below + instantiate_at_bvar + instantiate_bvar_at_below. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "lift_at_bvar_below".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_cancel_gen_bvar_above: generalized lift_cancel on a lifted bvar
        // at/above cutoff, given the positive witness after lifting.
        //
        // Proof strategy: rewrite lift_at's bvar case to `bvar (idx + 1)`,
        // derive the shifted zero witness from h_lift, unfold instantiate_at's
        // bvar case, use instantiate_bvar_at_above on the shifted index, then
        // rewrite `(idx + 1) - 1` back to `idx`.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_cancel_gen_bvar_above".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (val : KExpr) (cutoff : Nat), ",
                "Eq Nat (Nat.sub cutoff idx) Nat.zero -> ",
                "Eq Nat ",
                "(Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) (Nat.succ Nat.zero))) -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) val cutoff) ",
                "(KExpr.bvar idx)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (val : KExpr) (cutoff : Nat) ",
                "(h_lift : Eq Nat (Nat.sub cutoff idx) Nat.zero) ",
                "(h_inner : Eq Nat (Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) (Nat.succ Nat.zero)))) => ",
                "Eq.trans KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) val cutoff) ",
                "(instantiate_at (KExpr.bvar (Nat.add idx (Nat.succ Nat.zero))) val cutoff) ",
                "(KExpr.bvar idx) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => instantiate_at x val cutoff) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (Nat.add idx (Nat.succ Nat.zero))) ",
                "(lift_at_bvar_geq idx cutoff (Nat.succ Nat.zero) h_lift)) ",
                "(Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar (Nat.add idx (Nat.succ Nat.zero))) val cutoff) ",
                "(instantiate_bvar_at (Nat.add idx (Nat.succ Nat.zero)) cutoff val) ",
                "(KExpr.bvar idx) ",
                "(instantiate_at_bvar (Nat.add idx (Nat.succ Nat.zero)) val cutoff) ",
                "(Eq.trans KExpr ",
                "(instantiate_bvar_at (Nat.add idx (Nat.succ Nat.zero)) cutoff val) ",
                "(KExpr.bvar (Nat.sub (Nat.add idx (Nat.succ Nat.zero)) (Nat.succ Nat.zero))) ",
                "(KExpr.bvar idx) ",
                "(instantiate_bvar_at_above (Nat.add idx (Nat.succ Nat.zero)) cutoff val ",
                "(Eq.trans Nat ",
                "(Nat.sub cutoff (Nat.add idx (Nat.succ Nat.zero))) ",
                "(Nat.sub cutoff (Nat.succ idx)) ",
                "Nat.zero ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub cutoff x) ",
                "(Nat.add idx (Nat.succ Nat.zero)) ",
                "(Nat.succ idx) ",
                "(nat_add_succ_zero idx)) ",
                "(nat_sub_zero_implies_sub_succ_zero cutoff idx h_lift)) ",
                "h_inner) ",
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.sub (Nat.add idx (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) ",
                "idx ",
                "(nat_sub_add_succ_zero_one idx))))",
            )
            .to_string()),
            is_axiom: false,
            description: "Generalized lift_cancel bvar branch when idx >= cutoff, deriving the shifted zero witness and assuming only the positive witness after lifting. DerivedProved via lift_at_bvar_geq + instantiate_bvar_at_above + nat_sub_zero_implies_sub_succ_zero + nat_sub_add_succ_zero_one. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "nat_add_succ_zero".to_string(),
                "nat_sub_zero_implies_sub_succ_zero".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_sub_add_succ_zero_one".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
