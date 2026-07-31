// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Cutoff-generalized lift_at shift proofs split from expr_model_lift_shift.rs.
//!
//! Contains:
//!   - lift_at_shift_succ_bvar_gen (bvar case at arbitrary cutoff c)
//!   - lift_at_shift_succ_gen (full KExpr.rec proof)
//!   - lift_at_shift_succ (c=0 specialization, formerly HelperAxiom)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_shift_gen(&mut self) -> Result<(), SpecError> {
        // lift_at_shift_succ_bvar_gen: generalized bvar case with arbitrary cutoff c.
        //
        // Statement: lift(lift(bvar j, c, n), add(c,d), 1) = lift(bvar j, c, succ n)
        // when d <= n.
        //
        // Proof by Nat.rec convoy on sub(c, j):
        //   d=0 (j >= c): both lifts take geq branch, bridge via arithmetic.
        //   d=succ k (j < c): both lifts leave bvar j unchanged.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_shift_succ_bvar_gen".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c : Nat) (n : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub d n) Nat.zero -> ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar j) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                "(lift_at (KExpr.bvar j) c (Nat.succ n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (c : Nat) (n : Nat) (d : Nat) ",
                    "(h_dn : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (gap : Nat) => ",
                    "Eq Nat (Nat.sub c j) gap -> ",
                    "Eq KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n))) ",
                    // gap=0: j >= c (above cutoff)
                    "(fun (h0 : Eq Nat (Nat.sub c j) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar (Nat.add j n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c n) ",
                    "(KExpr.bvar (Nat.add j n)) ",
                    "(lift_at_bvar_geq j c n h0)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.bvar (Nat.add j n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(lift_at_bvar_geq (Nat.add j n) (Nat.add c d) (Nat.succ Nat.zero) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add c d) (Nat.add j n)) ",
                    "(Nat.sub (Nat.add c d) (Nat.add n j)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub (Nat.add c d) x) ",
                    "(Nat.add j n) (Nat.add n j) ",
                    "(nat_add_comm j n)) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add c d) (Nat.add n j)) ",
                    "(Nat.sub (Nat.add d c) (Nat.add n j)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.add n j)) ",
                    "(Nat.add c d) (Nat.add d c) ",
                    "(nat_add_comm c d)) ",
                    "(nat_sub_zero_add_monotone d n c j h_dn h0)))) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) (Nat.succ Nat.zero))) ",
                    "(KExpr.bvar (Nat.add j (Nat.succ n))) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
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
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(KExpr.bvar (Nat.add j (Nat.succ n))) ",
                    "(lift_at_bvar_geq j c (Nat.succ n) h0))))) ",
                    // gap=succ k: j < c (below cutoff)
                    "(fun (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub c j) k -> ",
                    "Eq KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n))) ",
                    "(h_sk : Eq Nat (Nat.sub c j) (Nat.succ k)) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.bvar j) c n) ",
                    "(KExpr.bvar j) ",
                    "(lift_at_bvar_below j c n ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c j) k h_sk))) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.bvar j) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.bvar j) ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(lift_at_bvar_below j (Nat.add c d) (Nat.succ Nat.zero) ",
                    "(nat_sub_pos_add_right c d j ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c j) k h_sk))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.bvar j) c (Nat.succ n)) ",
                    "(KExpr.bvar j) ",
                    "(lift_at_bvar_below j c (Nat.succ n) ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c j) k h_sk))))) ",
                    "(Nat.sub c j) ",
                    "(Eq.refl Nat (Nat.sub c j))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Generalized bvar case of lift_at_shift_succ at arbitrary cutoff c. ",
                "DerivedProved via Nat.rec convoy on sub(c,j). Part of #464.",
            )
            .to_string(),
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
                "nat_add_comm".to_string(),
                "nat_add_succ_right".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "nat_sub_zero_add_monotone".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_shift_succ_gen: cutoff-generalized version of lift_at_shift_succ.
        //
        // Statement: lift(lift(e, c, n), add(c,d), 1) = lift(e, c, succ n) when d <= n.
        //
        // Proof by KExpr.rec with motive universalizing c, n, d, h.
        //   sort: trivial (Eq.refl).
        //   bvar: delegate to lift_at_shift_succ_bvar_gen.
        //   app: unfold both sides via lift_at_app, apply ih_f and ih_a.
        //   lam/pi: unfold via lift_at_lam/pi, apply ih_ty at c and ih_body at
        //     succ c (with nat_succ_add transport for the outer cutoff).
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_shift_succ_gen".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (c : Nat) (n : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub d n) Nat.zero -> ",
                "Eq KExpr ",
                "(lift_at (lift_at e c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                "(lift_at e c (Nat.succ n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (c : Nat) (n : Nat) (d : Nat) ",
                    "(h_dn : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "KExpr.rec ",
                    "(fun (expr : KExpr) => forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr ",
                    "(lift_at (lift_at expr c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at expr c (Nat.succ n))) ",
                    // sort: trivial
                    "(fun (sv : Level) (c : Nat) (n : Nat) (d : Nat) ",
                    "(_ : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.refl KExpr (KExpr.sort sv)) ",
                    // bvar: delegate
                    "(fun (j : Nat) (c : Nat) (n : Nat) (d : Nat) ",
                    "(h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "lift_at_shift_succ_bvar_gen j c n d h) ",
                    // app: unfold both sides
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ih_f : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at f c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at f c (Nat.succ n))) ",
                    "(ih_a : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at a c (Nat.succ n))) ",
                    "(c : Nat) (n : Nat) (d : Nat) ",
                    "(h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.app f a) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.app (lift_at f c n) (lift_at a c n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.app f a) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.app f a) c n) ",
                    "(KExpr.app (lift_at f c n) (lift_at a c n)) ",
                    "(lift_at_app f a c n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.app (lift_at f c n) (lift_at a c n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.app (lift_at (lift_at f c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.app f a) c (Nat.succ n)) ",
                    "(lift_at_app (lift_at f c n) (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.app (lift_at (lift_at f c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero))) ",
                    "(KExpr.app (lift_at f c (Nat.succ n)) (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.app f a) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app x (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero))) ",
                    "(lift_at (lift_at f c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at f c (Nat.succ n)) ",
                    "(ih_f c n d h)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.app (lift_at f c (Nat.succ n)) (lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero))) ",
                    "(KExpr.app (lift_at f c (Nat.succ n)) (lift_at a c (Nat.succ n))) ",
                    "(lift_at (KExpr.app f a) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app (lift_at f c (Nat.succ n)) x) ",
                    "(lift_at (lift_at a c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at a c (Nat.succ n)) ",
                    "(ih_a c n d h)) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.app f a) c (Nat.succ n)) ",
                    "(KExpr.app (lift_at f c (Nat.succ n)) (lift_at a c (Nat.succ n))) ",
                    "(lift_at_app f a c (Nat.succ n))))))) ",
                    // lam
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n))) ",
                    "(ih_body : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at body c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at body c (Nat.succ n))) ",
                    "(c : Nat) (n : Nat) (d : Nat) ",
                    "(h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.lam ty body) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.lam (lift_at ty c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.lam ty body) c n) ",
                    "(KExpr.lam (lift_at ty c n) (lift_at body (Nat.succ c) n)) ",
                    "(lift_at_lam ty body c n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.lam (lift_at ty c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.lam (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ n)) ",
                    "(lift_at_lam (lift_at ty c n) (lift_at body (Nat.succ c) n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.lam (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.lam (lift_at ty c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam x (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n)) ",
                    "(ih_ty c n d h)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.lam (lift_at ty c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.lam (lift_at ty c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam (lift_at ty c (Nat.succ n)) x) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.add (Nat.succ c) d) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at (lift_at body (Nat.succ c) n) x (Nat.succ Nat.zero)) ",
                    "(Nat.succ (Nat.add c d)) ",
                    "(Nat.add (Nat.succ c) d) ",
                    "(Eq.symm Nat (Nat.add (Nat.succ c) d) (Nat.succ (Nat.add c d)) ",
                    "(nat_succ_add c d))) ",
                    "(ih_body (Nat.succ c) n d h))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ n)) ",
                    "(KExpr.lam (lift_at ty c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at_lam ty body c (Nat.succ n))))))) ",
                    // pi (identical structure to lam)
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n))) ",
                    "(ih_body : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at body c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at body c (Nat.succ n))) ",
                    "(c : Nat) (n : Nat) (d : Nat) ",
                    "(h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.pi ty body) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.pi (lift_at ty c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.pi ty body) c n) ",
                    "(KExpr.pi (lift_at ty c n) (lift_at body (Nat.succ c) n)) ",
                    "(lift_at_pi ty body c n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.pi (lift_at ty c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.pi (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ n)) ",
                    "(lift_at_pi (lift_at ty c n) (lift_at body (Nat.succ c) n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.pi (lift_at ty c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi x (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n)) ",
                    "(ih_ty c n d h)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (lift_at ty c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.pi (lift_at ty c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi (lift_at ty c (Nat.succ n)) x) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.add (Nat.succ c) d) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at (lift_at body (Nat.succ c) n) x (Nat.succ Nat.zero)) ",
                    "(Nat.succ (Nat.add c d)) ",
                    "(Nat.add (Nat.succ c) d) ",
                    "(Eq.symm Nat (Nat.add (Nat.succ c) d) (Nat.succ (Nat.add c d)) ",
                    "(nat_succ_add c d))) ",
                    "(ih_body (Nat.succ c) n d h))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ n)) ",
                    "(KExpr.pi (lift_at ty c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at_pi ty body c (Nat.succ n))))))) ",
                    // const: trivial
                    "(fun (nm : Name) (us : ListType Level) (c : Nat) (n : Nat) (d : Nat) ",
                    "(_ : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // let_ : three-field analogue of lam/pi. ty and val recurse at
                    // cutoff c (like ty in lam); body at Nat.succ c with the same
                    // nat_succ_add transport on the outer cutoff. Chain
                    // START -> M1 -> M2 -> M3 -> M4 -> M5 -> END (one extra
                    // val-field rewrite vs lam).
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n))) ",
                    "(ih_val : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at val c (Nat.succ n))) ",
                    "(ih_body : forall (c : Nat) (n : Nat) (d : Nat), ",
                    "Eq Nat (Nat.sub d n) Nat.zero -> ",
                    "Eq KExpr (lift_at (lift_at body c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at body c (Nat.succ n))) ",
                    "(c : Nat) (n : Nat) (d : Nat) ",
                    "(h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.let_ ty val body) c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.let_ (lift_at ty c n) (lift_at val c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at (KExpr.let_ ty val body) c n) ",
                    "(KExpr.let_ (lift_at ty c n) (lift_at val c n) (lift_at body (Nat.succ c) n)) ",
                    "(lift_at_let_ ty val body c n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.let_ (lift_at ty c n) (lift_at val c n) (lift_at body (Nat.succ c) n)) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(KExpr.let_ (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(lift_at_let_ (lift_at ty c n) (lift_at val c n) (lift_at body (Nat.succ c) n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ x (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (lift_at ty c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at ty c (Nat.succ n)) ",
                    "(ih_ty c n d h)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at val c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ (lift_at ty c (Nat.succ n)) x (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(lift_at (lift_at val c n) (Nat.add c d) (Nat.succ Nat.zero)) ",
                    "(lift_at val c (Nat.succ n)) ",
                    "(ih_val c n d h)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at val c (Nat.succ n)) (lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero))) ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at val c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at val c (Nat.succ n)) x) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.succ (Nat.add c d)) (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at body (Nat.succ c) n) (Nat.add (Nat.succ c) d) (Nat.succ Nat.zero)) ",
                    "(lift_at body (Nat.succ c) (Nat.succ n)) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at (lift_at body (Nat.succ c) n) x (Nat.succ Nat.zero)) ",
                    "(Nat.succ (Nat.add c d)) ",
                    "(Nat.add (Nat.succ c) d) ",
                    "(Eq.symm Nat (Nat.add (Nat.succ c) d) (Nat.succ (Nat.add c d)) ",
                    "(nat_succ_add c d))) ",
                    "(ih_body (Nat.succ c) n d h))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ n)) ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ n)) (lift_at val c (Nat.succ n)) (lift_at body (Nat.succ c) (Nat.succ n))) ",
                    "(lift_at_let_ ty val body c (Nat.succ n)))))))) ",
                    // proj branch: 1-child node; ih_sub congruence (lift_at reduces through proj).
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : forall (c : Nat) (n : Nat) (d : Nat), Eq Nat (Nat.sub d n) Nat.zero -> Eq KExpr (lift_at (lift_at sub c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at sub c (Nat.succ n))) ",
                    "(c : Nat) (n : Nat) (d : Nat) (h : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at (lift_at sub c n) (Nat.add c d) (Nat.succ Nat.zero)) (lift_at sub c (Nat.succ n)) (ih_sub c n d h)) ",
                    // lit branch: leaf.
                    "(fun (m : Nat) (c : Nat) (n : Nat) (d : Nat) (_ : Eq Nat (Nat.sub d n) Nat.zero) => Eq.refl KExpr (KExpr.lit m)) ",
                    "e c n d h_dn",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "lift(lift(e, c, n), add(c,d), 1) = lift(e, c, succ n) when d <= n. ",
                "DerivedProved via cutoff-universalized KExpr.rec. Part of #464.",
            )
            .to_string(),
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
                "lift_at_lam".to_string(),
                "lift_at_let_".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_shift_succ_bvar_gen".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_shift_succ: the c=0 specialization of lift_at_shift_succ_gen.
        //
        // The original statement fixes the inner cutoff at 0. The generalized
        // version with cutoff c has been proved above. This corollary rewrites
        // add(0, d) = d via nat_zero_add to recover the original shape.
        //
        // Formerly a HelperAxiom — now DerivedProved. Part of #464.
        self.add_definition(SpecDefinition {
            name: "lift_at_shift_succ".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (n : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub d n) Nat.zero -> ",
                "Eq KExpr ",
                "(lift_at (lift_at e Nat.zero n) d (Nat.succ Nat.zero)) ",
                "(lift_at e Nat.zero (Nat.succ n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (n : Nat) (d : Nat) ",
                    "(h_dn : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at e Nat.zero n) d (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at e Nat.zero n) (Nat.add Nat.zero d) (Nat.succ Nat.zero)) ",
                    "(lift_at e Nat.zero (Nat.succ n)) ",
                    "(Eq.cong Nat KExpr ",
                    "(fun (x : Nat) => lift_at (lift_at e Nat.zero n) x (Nat.succ Nat.zero)) ",
                    "d (Nat.add Nat.zero d) ",
                    "(Eq.symm Nat (Nat.add Nat.zero d) d (nat_zero_add d))) ",
                    "(lift_at_shift_succ_gen e Nat.zero n d h_dn)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "lift(lift(e, 0, n), d, 1) = lift(e, 0, succ n) when d <= n. ",
                "DerivedProved as c=0 specialization of lift_at_shift_succ_gen ",
                "with nat_zero_add rewrite. Formerly a HelperAxiom. Part of #464.",
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
                "lift_at_shift_succ_gen".to_string(),
                "nat_zero_add".to_string(),
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
    fn test_lift_at_shift_succ_is_derived_proved() {
        let spec = build_spec_with_stack();

        let general = spec
            .definitions()
            .get("lift_at_shift_succ")
            .expect("lift_at_shift_succ should exist");
        assert!(
            !general.is_axiom,
            "lift_at_shift_succ should no longer be a helper axiom"
        );
        assert!(
            general.value_src.is_some(),
            "lift_at_shift_succ should carry a proof term (c=0 specialization)"
        );
        assert_eq!(
            general.proof_status,
            ProofStatus::DerivedProved,
            "lift_at_shift_succ should be DerivedProved"
        );
        assert!(
            general.axiom_deps.is_empty(),
            "lift_at_shift_succ should have no remaining axiom deps: {:?}",
            general.axiom_deps
        );
    }
}
