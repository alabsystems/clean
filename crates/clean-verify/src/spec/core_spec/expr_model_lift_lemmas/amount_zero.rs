// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_lift_zero_lemmas(&mut self) -> Result<(), SpecError> {
        // lift_at_amount_zero: lifting by 0 is identity on any expression.
        //
        // Proof strategy: KExpr.rec structural induction with cutoff-universalized
        // motive (fun e => forall c, lift_at e c 0 = e). Each branch uses the
        // existing per-constructor unfolding lemma (lift_at_app, lift_at_lam, etc.)
        // then two Eq.cong steps to rewrite each sub-expression via the IH. The
        // lam/pi branches use ih_body (Nat.succ c) since lift_at increments cutoff
        // under binders. Registered via add_definition_structural to bypass the
        // kernel's iota false negative on KExpr.rec motive application.
        // Part of #464, #461.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_amount_zero".to_string(),
            type_src: "forall (e : KExpr) (cutoff : Nat), Eq KExpr (lift_at e cutoff Nat.zero) e"
                .to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (cutoff : Nat) => ",
                "KExpr.rec ",
                // motive: universalize cutoff so lam/pi IH works at Nat.succ c
                "(fun (e : KExpr) => forall (c : Nat), Eq KExpr (lift_at e c Nat.zero) e) ",
                // sort branch: lift_at (sort n) c 0 = sort n by match reduction
                "(fun (n : Level) (c : Nat) => Eq.refl KExpr (KExpr.sort n)) ",
                // bvar branch: lift_at (bvar i) c 0 = bvar i via lift_bvar_at_amount_zero
                "(fun (i : Nat) (c : Nat) => lift_bvar_at_amount_zero i c) ",
                // app branch: Eq.trans lift_at_app (Eq.trans (cong ih_f) (cong ih_a))
                "(fun (f : KExpr) (a : KExpr) ",
                "(ih_f : forall (c : Nat), Eq KExpr (lift_at f c Nat.zero) f) ",
                "(ih_a : forall (c : Nat), Eq KExpr (lift_at a c Nat.zero) a) ",
                "(c : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (KExpr.app f a) c Nat.zero) ",
                "(KExpr.app (lift_at f c Nat.zero) (lift_at a c Nat.zero)) ",
                "(KExpr.app f a) ",
                "(lift_at_app f a c Nat.zero) ",
                "(Eq.trans KExpr ",
                "(KExpr.app (lift_at f c Nat.zero) (lift_at a c Nat.zero)) ",
                "(KExpr.app f (lift_at a c Nat.zero)) ",
                "(KExpr.app f a) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.app x (lift_at a c Nat.zero)) ",
                "(lift_at f c Nat.zero) f (ih_f c)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.app f x) ",
                "(lift_at a c Nat.zero) a (ih_a c)))) ",
                // lam branch: Eq.trans lift_at_lam (Eq.trans (cong ih_ty) (cong ih_body (succ c)))
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat), Eq KExpr (lift_at ty c Nat.zero) ty) ",
                "(ih_body : forall (c : Nat), Eq KExpr (lift_at body c Nat.zero) body) ",
                "(c : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (KExpr.lam ty body) c Nat.zero) ",
                "(KExpr.lam (lift_at ty c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.lam ty body) ",
                "(lift_at_lam ty body c Nat.zero) ",
                "(Eq.trans KExpr ",
                "(KExpr.lam (lift_at ty c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.lam ty (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.lam ty body) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.lam x (lift_at body (Nat.succ c) Nat.zero)) ",
                "(lift_at ty c Nat.zero) ty (ih_ty c)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.lam ty x) ",
                "(lift_at body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c))))) ",
                // pi branch: same pattern as lam
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat), Eq KExpr (lift_at ty c Nat.zero) ty) ",
                "(ih_body : forall (c : Nat), Eq KExpr (lift_at body c Nat.zero) body) ",
                "(c : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (KExpr.pi ty body) c Nat.zero) ",
                "(KExpr.pi (lift_at ty c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.pi ty body) ",
                "(lift_at_pi ty body c Nat.zero) ",
                "(Eq.trans KExpr ",
                "(KExpr.pi (lift_at ty c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.pi ty (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.pi ty body) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.pi x (lift_at body (Nat.succ c) Nat.zero)) ",
                "(lift_at ty c Nat.zero) ty (ih_ty c)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.pi ty x) ",
                "(lift_at body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c))))) ",
                // const branch: lift_at leaves constants unchanged
                "(fun (n : Name) (us : ListType Level) (c : Nat) => Eq.refl KExpr (KExpr.const n us)) ",
                // let_ branch: same pattern as lam/pi but with three congruence
                // steps (ty, val, body). ty and val recurse at cutoff c, body at
                // Nat.succ c since lift_at increments the cutoff under the binder.
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                "(ih_ty : forall (c : Nat), Eq KExpr (lift_at ty c Nat.zero) ty) ",
                "(ih_val : forall (c : Nat), Eq KExpr (lift_at val c Nat.zero) val) ",
                "(ih_body : forall (c : Nat), Eq KExpr (lift_at body c Nat.zero) body) ",
                "(c : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (KExpr.let_ ty val body) c Nat.zero) ",
                "(KExpr.let_ (lift_at ty c Nat.zero) (lift_at val c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.let_ ty val body) ",
                "(lift_at_let_ ty val body c Nat.zero) ",
                "(Eq.trans KExpr ",
                "(KExpr.let_ (lift_at ty c Nat.zero) (lift_at val c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.let_ ty (lift_at val c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.let_ ty val body) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ x (lift_at val c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(lift_at ty c Nat.zero) ty (ih_ty c)) ",
                "(Eq.trans KExpr ",
                "(KExpr.let_ ty (lift_at val c Nat.zero) (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.let_ ty val (lift_at body (Nat.succ c) Nat.zero)) ",
                "(KExpr.let_ ty val body) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ ty x (lift_at body (Nat.succ c) Nat.zero)) ",
                "(lift_at val c Nat.zero) val (ih_val c)) ",
                "(Eq.cong KExpr KExpr ",
                "(fun (x : KExpr) => KExpr.let_ ty val x) ",
                "(lift_at body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c)))))) ",
                // proj branch: 1-child node. lift_at (proj s i sub) c 0 reduces to
                // proj s i (lift_at sub c 0) (Eq.refl), then ih_sub via cong.
                "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                "(ih_sub : forall (c : Nat), Eq KExpr (lift_at sub c Nat.zero) sub) ",
                "(c : Nat) => ",
                "Eq.trans KExpr ",
                "(lift_at (KExpr.proj s i sub) c Nat.zero) ",
                "(KExpr.proj s i (lift_at sub c Nat.zero)) ",
                "(KExpr.proj s i sub) ",
                "(Eq.refl KExpr (KExpr.proj s i (lift_at sub c Nat.zero))) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at sub c Nat.zero) sub (ih_sub c))) ",
                // lit branch: leaf. lift_at (lit n) c 0 = lit n.
                "(fun (n : Nat) (c : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                // major premise + cutoff application
                "e cutoff",
            ).to_string()),
            is_axiom: false,
            description: "Lifting by amount 0 is identity for any expression. DerivedProved via KExpr.rec structural induction with cutoff-universalized motive + per-constructor unfolding lemmas. Part of #464, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_let_".to_string(),
                "lift_bvar_at_amount_zero".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
