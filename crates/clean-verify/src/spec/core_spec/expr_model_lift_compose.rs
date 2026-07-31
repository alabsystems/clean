// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! lift_at composition lemmas (split from expr_model_lift_lemmas.rs)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_compose(&mut self) -> Result<(), SpecError> {
        // nat_add_assoc: (a + b) + c = a + (b + c)
        //
        // Since Nat.add recurses on the third argument here, induction on c
        // keeps both sides definitionally aligned in the step branch: each
        // reduces to Nat.succ applied to the IH sides. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_add_assoc".to_string(),
            type_src: "forall (a : Nat) (b : Nat) (c : Nat), Eq Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))"
                .to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (c : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))) ",
                "(Eq.refl Nat (Nat.add a b)) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))) => ",
                "Eq.cong Nat Nat Nat.succ ",
                "(Nat.add (Nat.add a b) k) ",
                "(Nat.add a (Nat.add b k)) ",
                "ih) ",
                "c",
            ).to_string()),
            is_axiom: false,
            description: "(a + b) + c = a + (b + c). DerivedProved via Nat.rec on the third addend. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_zero_add_right: if cutoff <= idx, then cutoff <= idx + amount.
        //
        // Proof by Nat.rec on amount. The step case uses
        // nat_sub_zero_implies_sub_succ_zero after the defining iota reduction
        // Nat.add idx (succ k) = succ (Nat.add idx k). Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_add_right".to_string(),
            type_src: concat!(
                "forall (cutoff : Nat) (idx : Nat) (amount : Nat), ",
                "Eq Nat (Nat.sub cutoff idx) Nat.zero -> ",
                "Eq Nat (Nat.sub cutoff (Nat.add idx amount)) Nat.zero",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (cutoff : Nat) (idx : Nat) (amount : Nat) ",
                "(h : Eq Nat (Nat.sub cutoff idx) Nat.zero) => ",
                "Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub cutoff (Nat.add idx k)) Nat.zero) ",
                "h ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.sub cutoff (Nat.add idx k)) Nat.zero) => ",
                "nat_sub_zero_implies_sub_succ_zero cutoff (Nat.add idx k) ih) ",
                "amount",
            ).to_string()),
            is_axiom: false,
            description: "If cutoff <= idx then cutoff <= idx + amount. DerivedProved via Nat.rec on the added amount. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "nat_sub_zero_implies_sub_succ_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_compose_bvar: composing two lifts at the same cutoff on a bvar
        // is equivalent to one lift by the summed amount.
        //
        // Proof strategy: Nat.rec convoy on sub cutoff idx.
        //   d=0 (idx >= cutoff): both lifts take the geq branch, and nat_add_assoc
        //     re-associates the accumulated shift.
        //   d=succ k (idx < cutoff): every lift stays below cutoff, so all terms
        //     collapse to bvar idx through the below lemmas.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_compose_bvar".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (cutoff : Nat) (amount1 : Nat) (amount2 : Nat), ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar idx) cutoff amount1) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (cutoff : Nat) (amount1 : Nat) (amount2 : Nat) => ",
                "Nat.rec ",
                "(fun (d : Nat) => ",
                "Eq Nat (Nat.sub cutoff idx) d -> ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar idx) cutoff amount1) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2))) ",
                // d = 0: idx >= cutoff
                "(fun (h0 : Eq Nat (Nat.sub cutoff idx) Nat.zero) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.bvar idx) cutoff amount1) cutoff amount2) ",
                "(lift_at (KExpr.bvar (Nat.add idx amount1)) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff amount1) ",
                "(KExpr.bvar (Nat.add idx amount1)) ",
                "(lift_at_bvar_geq idx cutoff amount1 h0)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.bvar (Nat.add idx amount1)) cutoff amount2) ",
                "(KExpr.bvar (Nat.add (Nat.add idx amount1) amount2)) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(lift_at_bvar_geq (Nat.add idx amount1) cutoff amount2 ",
                "(nat_sub_zero_add_right cutoff idx amount1 h0)) ",
                "(Eq.trans KExpr ",
                "(KExpr.bvar (Nat.add (Nat.add idx amount1) amount2)) ",
                "(KExpr.bvar (Nat.add idx (Nat.add amount1 amount2))) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(Eq.cong Nat KExpr KExpr.bvar ",
                "(Nat.add (Nat.add idx amount1) amount2) ",
                "(Nat.add idx (Nat.add amount1 amount2)) ",
                "(nat_add_assoc idx amount1 amount2)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(KExpr.bvar (Nat.add idx (Nat.add amount1 amount2))) ",
                "(lift_at_bvar_geq idx cutoff (Nat.add amount1 amount2) h0))))) ",
                // d = succ k: idx < cutoff
                "(fun (k : Nat) ",
                "(_ : Eq Nat (Nat.sub cutoff idx) k -> ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar idx) cutoff amount1) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2))) ",
                "(h_sk : Eq Nat (Nat.sub cutoff idx) (Nat.succ k)) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.bvar idx) cutoff amount1) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x cutoff amount2) ",
                "(lift_at (KExpr.bvar idx) cutoff amount1) ",
                "(KExpr.bvar idx) ",
                "(lift_at_bvar_below idx cutoff amount1 ",
                "(nat_pos_witness_from_succ_eq (Nat.sub cutoff idx) k h_sk))) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.bvar idx) cutoff amount2) ",
                "(KExpr.bvar idx) ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(lift_at_bvar_below idx cutoff amount2 ",
                "(nat_pos_witness_from_succ_eq (Nat.sub cutoff idx) k h_sk)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.bvar idx) cutoff (Nat.add amount1 amount2)) ",
                "(KExpr.bvar idx) ",
                "(lift_at_bvar_below idx cutoff (Nat.add amount1 amount2) ",
                "(nat_pos_witness_from_succ_eq (Nat.sub cutoff idx) k h_sk))))) ",
                "(Nat.sub cutoff idx) ",
                "(Eq.refl Nat (Nat.sub cutoff idx))",
            ).to_string()),
            is_axiom: false,
            description: "Composing two lifts at the same cutoff on a bvar equals one lift by the summed amount. DerivedProved via Nat.rec convoy on the cutoff comparison. Part of #464.".to_string(),
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
                "lift_at_bvar_below".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_add_assoc".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_zero_add_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_compose: composing two lifts at the same cutoff is equivalent
        // to one lift by the summed amount.
        //
        // Proof strategy: cutoff/amount-universalized KExpr.rec. The bvar branch
        // uses lift_at_compose_bvar; app/lam/pi rewrite both lift shells with the
        // structural lemmas, then apply the IH pointwise. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_compose".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (cutoff : Nat) (amount1 : Nat) (amount2 : Nat), ",
                "Eq KExpr ",
                "(lift_at (lift_at e cutoff amount1) cutoff amount2) ",
                "(lift_at e cutoff (Nat.add amount1 amount2))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (cutoff : Nat) (amount1 : Nat) (amount2 : Nat) => ",
                "KExpr.rec ",
                "(fun (expr : KExpr) => forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr ",
                "(lift_at (lift_at expr c a1) c a2) ",
                "(lift_at expr c (Nat.add a1 a2))) ",
                // sort
                "(fun (n : Level) (c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.refl KExpr (KExpr.sort n)) ",
                // bvar
                "(fun (idx : Nat) (c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "lift_at_compose_bvar idx c a1 a2) ",
                // app
                "(fun (f : KExpr) (a : KExpr) ",
                "(ih_f : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at f c a1) c a2) (lift_at f c (Nat.add a1 a2))) ",
                "(ih_a : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at a c a1) c a2) (lift_at a c (Nat.add a1 a2))) ",
                "(c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.app f a) c a1) c a2) ",
                "(lift_at (KExpr.app (lift_at f c a1) (lift_at a c a1)) c a2) ",
                "(lift_at (KExpr.app f a) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x c a2) ",
                "(lift_at (KExpr.app f a) c a1) ",
                "(KExpr.app (lift_at f c a1) (lift_at a c a1)) ",
                "(lift_at_app f a c a1)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.app (lift_at f c a1) (lift_at a c a1)) c a2) ",
                "(KExpr.app (lift_at (lift_at f c a1) c a2) (lift_at (lift_at a c a1) c a2)) ",
                "(lift_at (KExpr.app f a) c (Nat.add a1 a2)) ",
                "(lift_at_app (lift_at f c a1) (lift_at a c a1) c a2) ",
                "(Eq.trans KExpr ",
                "(KExpr.app (lift_at (lift_at f c a1) c a2) (lift_at (lift_at a c a1) c a2)) ",
                "(KExpr.app (lift_at f c (Nat.add a1 a2)) (lift_at (lift_at a c a1) c a2)) ",
                "(lift_at (KExpr.app f a) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.app x (lift_at (lift_at a c a1) c a2)) ",
                "(lift_at (lift_at f c a1) c a2) ",
                "(lift_at f c (Nat.add a1 a2)) ",
                "(ih_f c a1 a2)) ",
                "(Eq.trans KExpr ",
                "(KExpr.app (lift_at f c (Nat.add a1 a2)) (lift_at (lift_at a c a1) c a2)) ",
                "(KExpr.app (lift_at f c (Nat.add a1 a2)) (lift_at a c (Nat.add a1 a2))) ",
                "(lift_at (KExpr.app f a) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.app (lift_at f c (Nat.add a1 a2)) x) ",
                "(lift_at (lift_at a c a1) c a2) ",
                "(lift_at a c (Nat.add a1 a2)) ",
                "(ih_a c a1 a2)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.app f a) c (Nat.add a1 a2)) ",
                "(KExpr.app (lift_at f c (Nat.add a1 a2)) (lift_at a c (Nat.add a1 a2))) ",
                "(lift_at_app f a c (Nat.add a1 a2))))))) ",
                // lam
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at ty c a1) c a2) (lift_at ty c (Nat.add a1 a2))) ",
                "(ih_body : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at body c a1) c a2) (lift_at body c (Nat.add a1 a2))) ",
                "(c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.lam ty body) c a1) c a2) ",
                "(lift_at (KExpr.lam (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(lift_at (KExpr.lam ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x c a2) ",
                "(lift_at (KExpr.lam ty body) c a1) ",
                "(KExpr.lam (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) ",
                "(lift_at_lam ty body c a1)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.lam (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(KExpr.lam (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.lam ty body) c (Nat.add a1 a2)) ",
                "(lift_at_lam (lift_at ty c a1) (lift_at body (Nat.succ c) a1) c a2) ",
                "(Eq.trans KExpr ",
                "(KExpr.lam (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.lam (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.lam ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.lam x (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (lift_at ty c a1) c a2) ",
                "(lift_at ty c (Nat.add a1 a2)) ",
                "(ih_ty c a1 a2)) ",
                "(Eq.trans KExpr ",
                "(KExpr.lam (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.lam (lift_at ty c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at (KExpr.lam ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.lam (lift_at ty c (Nat.add a1 a2)) x) ",
                "(lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2) ",
                "(lift_at body (Nat.succ c) (Nat.add a1 a2)) ",
                "(ih_body (Nat.succ c) a1 a2)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.lam ty body) c (Nat.add a1 a2)) ",
                "(KExpr.lam (lift_at ty c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at_lam ty body c (Nat.add a1 a2))))))) ",
                // pi
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at ty c a1) c a2) (lift_at ty c (Nat.add a1 a2))) ",
                "(ih_body : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at body c a1) c a2) (lift_at body c (Nat.add a1 a2))) ",
                "(c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.pi ty body) c a1) c a2) ",
                "(lift_at (KExpr.pi (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(lift_at (KExpr.pi ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x c a2) ",
                "(lift_at (KExpr.pi ty body) c a1) ",
                "(KExpr.pi (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) ",
                "(lift_at_pi ty body c a1)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.pi (lift_at ty c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(KExpr.pi (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.pi ty body) c (Nat.add a1 a2)) ",
                "(lift_at_pi (lift_at ty c a1) (lift_at body (Nat.succ c) a1) c a2) ",
                "(Eq.trans KExpr ",
                "(KExpr.pi (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.pi (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.pi ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.pi x (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (lift_at ty c a1) c a2) ",
                "(lift_at ty c (Nat.add a1 a2)) ",
                "(ih_ty c a1 a2)) ",
                "(Eq.trans KExpr ",
                "(KExpr.pi (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.pi (lift_at ty c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at (KExpr.pi ty body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.pi (lift_at ty c (Nat.add a1 a2)) x) ",
                "(lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2) ",
                "(lift_at body (Nat.succ c) (Nat.add a1 a2)) ",
                "(ih_body (Nat.succ c) a1 a2)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.pi ty body) c (Nat.add a1 a2)) ",
                "(KExpr.pi (lift_at ty c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at_pi ty body c (Nat.add a1 a2))))))) ",
                // const
                "(fun (nm : Name) (us : ListType Level) (c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.refl KExpr (KExpr.const nm us)) ",
                // let_ : three-field analogue of lam/pi. ty and val recurse at
                // cutoff c, body at Nat.succ c. Chain START -> M1 -> M2 -> M3 ->
                // M4 -> M5 -> END (one extra val-field rewrite vs lam).
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at ty c a1) c a2) (lift_at ty c (Nat.add a1 a2))) ",
                "(ih_val : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at val c a1) c a2) (lift_at val c (Nat.add a1 a2))) ",
                "(ih_body : forall (c : Nat) (a1 : Nat) (a2 : Nat), ",
                "Eq KExpr (lift_at (lift_at body c a1) c a2) (lift_at body c (Nat.add a1 a2))) ",
                "(c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (lift_at (KExpr.let_ ty val body) c a1) c a2) ",
                "(lift_at (KExpr.let_ (lift_at ty c a1) (lift_at val c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => lift_at x c a2) ",
                "(lift_at (KExpr.let_ ty val body) c a1) ",
                "(KExpr.let_ (lift_at ty c a1) (lift_at val c a1) (lift_at body (Nat.succ c) a1)) ",
                "(lift_at_let_ ty val body c a1)) ",
                "(Eq.trans KExpr ",
                "(lift_at (KExpr.let_ (lift_at ty c a1) (lift_at val c a1) (lift_at body (Nat.succ c) a1)) c a2) ",
                "(KExpr.let_ (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at val c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(lift_at_let_ (lift_at ty c a1) (lift_at val c a1) (lift_at body (Nat.succ c) a1) c a2) ",
                "(Eq.trans KExpr ",
                "(KExpr.let_ (lift_at (lift_at ty c a1) c a2) (lift_at (lift_at val c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at val c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ x (lift_at (lift_at val c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (lift_at ty c a1) c a2) ",
                "(lift_at ty c (Nat.add a1 a2)) ",
                "(ih_ty c a1 a2)) ",
                "(Eq.trans KExpr ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at (lift_at val c a1) c a2) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at val c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ (lift_at ty c (Nat.add a1 a2)) x (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(lift_at (lift_at val c a1) c a2) ",
                "(lift_at val c (Nat.add a1 a2)) ",
                "(ih_val c a1 a2)) ",
                "(Eq.trans KExpr ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at val c (Nat.add a1 a2)) (lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2)) ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at val c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at val c (Nat.add a1 a2)) x) ",
                "(lift_at (lift_at body (Nat.succ c) a1) (Nat.succ c) a2) ",
                "(lift_at body (Nat.succ c) (Nat.add a1 a2)) ",
                "(ih_body (Nat.succ c) a1 a2)) ",
                "(Eq.symm KExpr ",
                "(lift_at (KExpr.let_ ty val body) c (Nat.add a1 a2)) ",
                "(KExpr.let_ (lift_at ty c (Nat.add a1 a2)) (lift_at val c (Nat.add a1 a2)) (lift_at body (Nat.succ c) (Nat.add a1 a2))) ",
                "(lift_at_let_ ty val body c (Nat.add a1 a2)))))))) ",
                // proj branch: 1-child node. lift_at reduces through proj (defeq),
                // so ih_sub congruence under (proj s i _) discharges the goal.
                "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                "(ih_sub : forall (c : Nat) (a1 : Nat) (a2 : Nat), Eq KExpr (lift_at (lift_at sub c a1) c a2) (lift_at sub c (Nat.add a1 a2))) ",
                "(c : Nat) (a1 : Nat) (a2 : Nat) => ",
                "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at (lift_at sub c a1) c a2) (lift_at sub c (Nat.add a1 a2)) (ih_sub c a1 a2)) ",
                // lit branch: leaf.
                "(fun (n : Nat) (c : Nat) (a1 : Nat) (a2 : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                "e cutoff amount1 amount2",
            ).to_string()),
            is_axiom: false,
            description: "Composing two lifts at the same cutoff equals one lift by the summed amount. DerivedProved via cutoff-universalized KExpr.rec. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "KExpr.rec".to_string(),
                "lift_at_app".to_string(),
                "lift_at_compose_bvar".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_let_".to_string(),
                "lift_at_pi".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn test_lift_compose_family_is_constructive() {
        let spec = build_spec_with_stack();

        for name in [
            "nat_add_assoc",
            "nat_sub_zero_add_right",
            "lift_at_compose_bvar",
            "lift_at_compose",
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
