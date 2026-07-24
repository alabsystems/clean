// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! lift_cancel derived proofs (split from expr_model_lift_lemmas.rs)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_cancel(&mut self) -> Result<(), SpecError> {
        // lift_cancel_gen_bvar: the bvar case of lift_cancel_gen.
        //
        // Proof strategy: Nat.rec convoy pattern on d = sub cutoff idx.
        //   d=0 (above case): idx >= cutoff. Lift adds 1, instantiate_bvar_at_above
        //     decrements. Positive witness derived from nat_sub_pos_witness,
        //     transported through nat_add_succ_zero (succ idx -> add idx 1).
        //   d=succ k (below case): idx < cutoff. Lift preserves bvar idx,
        //     instantiate_bvar_at_below preserves. Positivity form reconstructed
        //     from h_sk via nat_sub_succ_one.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_cancel_gen_bvar".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (val : KExpr) (cutoff : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar idx) cutoff (Nat.succ Nat.zero)) val cutoff) ",
                "(KExpr.bvar idx)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (idx : Nat) (val : KExpr) (cutoff : Nat) => ",
                    // Nat.rec convoy on sub cutoff idx
                    "Nat.rec ",
                    // motive: convoy pattern — carry hypothesis d = sub cutoff idx
                    "(fun (d : Nat) => ",
                    "Eq Nat (Nat.sub cutoff idx) d -> ",
                    "Eq KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar idx) cutoff ",
                    "(Nat.succ Nat.zero)) val cutoff) ",
                    "(KExpr.bvar idx)) ",
                    //
                    // === d=0 case (above): idx >= cutoff ===
                    //
                    "(fun (h0 : Eq Nat (Nat.sub cutoff idx) Nat.zero) => ",
                    "lift_cancel_gen_bvar_above idx val cutoff h0 ",
                    // h_inner: sub (add idx 1) cutoff = succ (sub (sub (add idx 1) cutoff) 1)
                    // Derived by transporting nat_sub_pos_witness via nat_add_succ_zero
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ idx) cutoff) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) ",
                    "(Nat.succ Nat.zero))) ",
                    // step 1: add idx 1 → succ idx → nat_sub_pos_witness result
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add idx (Nat.succ Nat.zero)) cutoff) ",
                    "(Nat.sub (Nat.succ idx) cutoff) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ idx) cutoff) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x cutoff) ",
                    "(Nat.add idx (Nat.succ Nat.zero)) ",
                    "(Nat.succ idx) ",
                    "(nat_add_succ_zero idx)) ",
                    "(nat_sub_pos_witness cutoff idx h0)) ",
                    // step 2: replace succ idx → add idx 1 in RHS
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub (Nat.sub x cutoff) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Nat.succ idx) ",
                    "(Nat.add idx (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.add idx (Nat.succ Nat.zero)) ",
                    "(Nat.succ idx) ",
                    "(nat_add_succ_zero idx))))) ",
                    //
                    // === d=succ k case (below): idx < cutoff ===
                    //
                    "(fun (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub cutoff idx) k -> ",
                    "Eq KExpr ",
                    "(instantiate_at (lift_at (KExpr.bvar idx) cutoff ",
                    "(Nat.succ Nat.zero)) val cutoff) ",
                    "(KExpr.bvar idx)) ",
                    "(h_sk : Eq Nat (Nat.sub cutoff idx) (Nat.succ k)) => ",
                    "lift_cancel_gen_bvar_below idx val cutoff ",
                    // h: sub cutoff idx = succ (sub (sub cutoff idx) 1)
                    // Derived from h_sk by rewriting k = sub (sub cutoff idx) 1
                    "(Eq.trans Nat ",
                    "(Nat.sub cutoff idx) ",
                    "(Nat.succ k) ",
                    "(Nat.succ (Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero))) ",
                    "h_sk ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ x) ",
                    "k ",
                    "(Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero)) ",
                    "k ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.sub cutoff idx) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ k) (Nat.succ Nat.zero)) ",
                    "k ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "(Nat.sub cutoff idx) ",
                    "(Nat.succ k) ",
                    "h_sk) ",
                    "(nat_sub_succ_one k)))))) ",
                    // major premise + reflexivity trigger
                    "(Nat.sub cutoff idx) ",
                    "(Eq.refl Nat (Nat.sub cutoff idx))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "lift_cancel_gen bvar case via Nat.rec convoy on sub cutoff idx. ",
                "Below: lift+instantiate preserves bvar. Above: lift adds 1, ",
                "instantiate decrements, nat_sub_pos_witness provides positive witness. ",
                "Part of #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_cancel_gen_bvar_above".to_string(),
                "lift_cancel_gen_bvar_below".to_string(),
                "nat_sub_pos_witness".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_sub_succ_one".to_string(),
                "Nat.rec".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_cancel_gen: generalized lift/instantiate cancellation.
        //
        // Proof strategy: KExpr.rec with a cutoff-universalized motive
        //   P e := forall val cutoff,
        //     instantiate_at (lift_at e cutoff 1) val cutoff = e.
        // The bvar branch is discharged by lift_cancel_gen_bvar. The app/lam/pi
        // branches first rewrite the outer lift/instantiate shells with the
        // structural lemmas, then apply the IH pointwise; lam/pi use the body IH
        // at Nat.succ cutoff because both lift_at and instantiate_at step under
        // binders. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_cancel_gen".to_string(),
            type_src: "forall (e : KExpr) (val : KExpr) (cutoff : Nat), Eq KExpr (instantiate_at (lift_at e cutoff (Nat.succ Nat.zero)) val cutoff) e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (val : KExpr) (cutoff : Nat) => ",
                    "KExpr.rec ",
                    "(fun (expr : KExpr) => forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at expr c (Nat.succ Nat.zero)) w c) expr) ",
                    // sort branch
                    "(fun (n : Level) (w : KExpr) (c : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.sort n) c (Nat.succ Nat.zero)) w c) ",
                    "(instantiate_at (KExpr.sort n) w c) ",
                    "(KExpr.sort n) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w c) ",
                    "(lift_at (KExpr.sort n) c (Nat.succ Nat.zero)) ",
                    "(KExpr.sort n) ",
                    "(lift_at_sort n c (Nat.succ Nat.zero))) ",
                    "(instantiate_at_sort n w c)) ",
                    // bvar branch
                    "(fun (idx : Nat) (w : KExpr) (c : Nat) => lift_cancel_gen_bvar idx w c) ",
                    // app branch
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ih_f : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at f c (Nat.succ Nat.zero)) w c) f) ",
                    "(ih_a : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c) a) ",
                    "(w : KExpr) (c : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.app f a) c (Nat.succ Nat.zero)) w c) ",
                    "(instantiate_at (KExpr.app (lift_at f c (Nat.succ Nat.zero)) (lift_at a c (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.app f a) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w c) ",
                    "(lift_at (KExpr.app f a) c (Nat.succ Nat.zero)) ",
                    "(KExpr.app (lift_at f c (Nat.succ Nat.zero)) (lift_at a c (Nat.succ Nat.zero))) ",
                    "(lift_at_app f a c (Nat.succ Nat.zero))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.app (lift_at f c (Nat.succ Nat.zero)) (lift_at a c (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.app (instantiate_at (lift_at f c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c)) ",
                    "(KExpr.app f a) ",
                    "(instantiate_at_app (lift_at f c (Nat.succ Nat.zero)) (lift_at a c (Nat.succ Nat.zero)) w c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.app (instantiate_at (lift_at f c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c)) ",
                    "(KExpr.app f (instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c)) ",
                    "(KExpr.app f a) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app x (instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c)) ",
                    "(instantiate_at (lift_at f c (Nat.succ Nat.zero)) w c) ",
                    "f ",
                    "(ih_f w c)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app f x) ",
                    "(instantiate_at (lift_at a c (Nat.succ Nat.zero)) w c) ",
                    "a ",
                    "(ih_a w c))))) ",
                    // lam branch
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ty) ",
                    "(ih_body : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at body c (Nat.succ Nat.zero)) w c) body) ",
                    "(w : KExpr) (c : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.lam ty body) c (Nat.succ Nat.zero)) w c) ",
                    "(instantiate_at (KExpr.lam (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.lam ty body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w c) ",
                    "(lift_at (KExpr.lam ty body) c (Nat.succ Nat.zero)) ",
                    "(KExpr.lam (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) ",
                    "(lift_at_lam ty body c (Nat.succ Nat.zero))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.lam (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.lam (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.lam ty body) ",
                    "(instantiate_at_lam (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.lam (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.lam ty (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.lam ty body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam x (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ",
                    "ty ",
                    "(ih_ty w c)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.lam ty x) ",
                    "(instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c)) ",
                    "body ",
                    "(ih_body w (Nat.succ c)))))) ",
                    // pi branch
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ty) ",
                    "(ih_body : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at body c (Nat.succ Nat.zero)) w c) body) ",
                    "(w : KExpr) (c : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.pi ty body) c (Nat.succ Nat.zero)) w c) ",
                    "(instantiate_at (KExpr.pi (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.pi ty body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w c) ",
                    "(lift_at (KExpr.pi ty body) c (Nat.succ Nat.zero)) ",
                    "(KExpr.pi (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) ",
                    "(lift_at_pi ty body c (Nat.succ Nat.zero))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.pi (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.pi (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.pi ty body) ",
                    "(instantiate_at_pi (lift_at ty c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.pi ty (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.pi ty body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi x (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ",
                    "ty ",
                    "(ih_ty w c)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.pi ty x) ",
                    "(instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c)) ",
                    "body ",
                    "(ih_body w (Nat.succ c)))))) ",
                    // const branch
                    "(fun (nm : Name) (us : ListType Level) (w : KExpr) (c : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // let_ branch: three-field analogue of lam/pi. ty and val
                    // cancel at cutoff c; body cancels at Nat.succ c because
                    // both lift_at and instantiate_at step under the binder.
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ty) ",
                    "(ih_val : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) val) ",
                    "(ih_body : forall (w : KExpr) (c : Nat), ",
                    "Eq KExpr (instantiate_at (lift_at body c (Nat.succ Nat.zero)) w c) body) ",
                    "(w : KExpr) (c : Nat) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at (KExpr.let_ ty val body) c (Nat.succ Nat.zero)) w c) ",
                    "(instantiate_at (KExpr.let_ (lift_at ty c (Nat.succ Nat.zero)) (lift_at val c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x w c) ",
                    "(lift_at (KExpr.let_ ty val body) c (Nat.succ Nat.zero)) ",
                    "(KExpr.let_ (lift_at ty c (Nat.succ Nat.zero)) (lift_at val c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) ",
                    "(lift_at_let_ ty val body c (Nat.succ Nat.zero))) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.let_ (lift_at ty c (Nat.succ Nat.zero)) (lift_at val c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero))) w c) ",
                    "(KExpr.let_ (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(instantiate_at_let_ (lift_at ty c (Nat.succ Nat.zero)) (lift_at val c (Nat.succ Nat.zero)) (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w c) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.let_ ty (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ x (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(instantiate_at (lift_at ty c (Nat.succ Nat.zero)) w c) ",
                    "ty ",
                    "(ih_ty w c)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ ty (instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.let_ ty val (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(KExpr.let_ ty val body) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty x (instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c))) ",
                    "(instantiate_at (lift_at val c (Nat.succ Nat.zero)) w c) ",
                    "val ",
                    "(ih_val w c)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.let_ ty val x) ",
                    "(instantiate_at (lift_at body (Nat.succ c) (Nat.succ Nat.zero)) w (Nat.succ c)) ",
                    "body ",
                    "(ih_body w (Nat.succ c))))))) ",
                    // proj: 1-child node; lift_at + instantiate_at reduce through proj, ih_sub cong.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : forall (w : KExpr) (c : Nat), Eq KExpr (instantiate_at (lift_at sub c (Nat.succ Nat.zero)) w c) sub) ",
                    "(w : KExpr) (c : Nat) => ",
                    "Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (instantiate_at (lift_at sub c (Nat.succ Nat.zero)) w c) sub (ih_sub w c)) ",
                    // lit: leaf.
                    "(fun (litn : Nat) (w : KExpr) (c : Nat) => Eq.refl KExpr (KExpr.lit litn)) ",
                    "e val cutoff",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Generalized lift_cancel at arbitrary cutoff. DerivedProved via cutoff-universalized KExpr.rec, with the bvar branch discharged constructively by lift_cancel_gen_bvar. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_at_let_".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_sort".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_let_".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_sort".to_string(),
                "lift_cancel_gen_bvar".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "lift_cancel".to_string(),
            type_src: "forall (e : KExpr) (val : KExpr), Eq KExpr (instantiate_at (lift_at e Nat.zero (Nat.succ Nat.zero)) val Nat.zero) e".to_string(),
            value_src: Some(
                "fun (e : KExpr) (val : KExpr) => lift_cancel_gen e val Nat.zero"
                    .to_string(),
            ),
            is_axiom: false,
            description: "lift_cancel: instantiate_at (lift_at e 0 1) val 0 = e. DerivedProved by specializing lift_cancel_gen at cutoff 0. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["lift_cancel_gen".to_string()])),
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
    fn test_lift_cancel_gen_bvar_is_constructive() {
        let spec = build_spec_with_stack();
        let def = spec
            .definitions()
            .get("lift_cancel_gen_bvar")
            .expect("Missing lift_cancel_gen_bvar");
        assert!(def.value_src.is_some(), "should have a proof term");
        assert!(!def.is_axiom, "should not be an axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "should have no remaining helper blockers: {:?}",
            def.axiom_deps
        );
    }

    #[test]
    fn test_lift_cancel_family_is_constructive() {
        let spec = build_spec_with_stack();

        for name in ["lift_cancel_gen", "lift_cancel"] {
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
