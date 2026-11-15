// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replacement independence at an absent de Bruijn index, consumed by the
//! existing projection-field body update. No closedness hypothesis is needed:
//! outer variables are still lowered, and binder bodies increment the index.
//! This proves substitution algebra, not Prop elimination, projection typing,
//! cache correctness, metadata admission or production Rust refinement.
//! The canonical occurrence, two positivity folds and return-parameter fold in
//! env_extensions.rs now use explicit parameter-general recursors; the old
//! match elaboration discarded changed recursive arguments. Controls here check
//! their actual results. Return-shape checks are not declaration typing proofs.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// Explicit checked theorem records; no source-parser/status promotion shortcut.
const PROOFS: &[(&str, &str, &str)] = &[
    (
        "projection_absent_nat_cases",
        r"forall (n : Nat) (C : Prop),
 (Eq Nat n Nat.zero -> C) -> (forall (k : Nat), Eq Nat n (Nat.succ k) -> C) -> C",
        r"fun (n : Nat) (C : Prop) => Nat.rec
 (fun (n0 : Nat) => (Eq Nat n0 Nat.zero -> C) ->
   (forall (k : Nat), Eq Nat n0 (Nat.succ k) -> C) -> C)
 (fun (hz : Eq Nat Nat.zero Nat.zero -> C)
   (_hs : forall (k : Nat), Eq Nat Nat.zero (Nat.succ k) -> C) => hz (Eq.refl Nat Nat.zero))
 (fun (k : Nat) (_ih : (Eq Nat k Nat.zero -> C) ->
   (forall (j : Nat), Eq Nat k (Nat.succ j) -> C) -> C)
   (_hz : Eq Nat (Nat.succ k) Nat.zero -> C)
   (hs : forall (j : Nat), Eq Nat (Nat.succ k) (Nat.succ j) -> C) =>
   hs k (Eq.refl Nat (Nat.succ k))) n",
    ),
    (
        "projection_absent_or_left",
        r"forall (a : Bool) (b : Bool), Eq Bool (Bool.or a b) Bool.false -> Eq Bool a Bool.false",
        r"fun (a : Bool) (b : Bool) => Bool.rec
 (fun (a0 : Bool) => Eq Bool (Bool.or a0 b) Bool.false -> Eq Bool a0 Bool.false)
 (fun (_h : Eq Bool (Bool.or Bool.false b) Bool.false) => Eq.refl Bool Bool.false)
 (fun (h : Eq Bool (Bool.or Bool.true b) Bool.false) => h) a",
    ),
    (
        "projection_absent_or_right",
        r"forall (a : Bool) (b : Bool), Eq Bool (Bool.or a b) Bool.false -> Eq Bool b Bool.false",
        r"fun (a : Bool) (b : Bool) => Bool.rec
 (fun (a0 : Bool) => Eq Bool (Bool.or a0 b) Bool.false -> Eq Bool b Bool.false)
 (fun (h : Eq Bool (Bool.or Bool.false b) Bool.false) => h)
 (fun (h : Eq Bool (Bool.or Bool.true b) Bool.false) =>
   bool_false_ne_true (Eq Bool b Bool.false)
     (Eq.symm Bool Bool.true Bool.false h)) a",
    ),
    (
        "projection_absent_bvar",
        r"forall (i : Nat) (d : Nat) (p : KExpr) (q : KExpr),
 Eq Bool (nat_eqb i d) Bool.false ->
 Eq KExpr (instantiate_bvar_at i d p) (instantiate_bvar_at i d q)",
        r"fun (i : Nat) (d : Nat) (p : KExpr) (q : KExpr)
 (h : Eq Bool (nat_eqb i d) Bool.false) =>
 projection_absent_nat_cases (Nat.sub d i)
 (Eq KExpr (instantiate_bvar_at i d p) (instantiate_bvar_at i d q))
 (fun (hd : Eq Nat (Nat.sub d i) Nat.zero) =>
   projection_absent_nat_cases (Nat.sub i d)
   (Eq KExpr (instantiate_bvar_at i d p) (instantiate_bvar_at i d q))
   (fun (hi : Eq Nat (Nat.sub i d) Nat.zero) =>
     bool_false_ne_true (Eq KExpr (instantiate_bvar_at i d p) (instantiate_bvar_at i d q))
     (Eq.trans Bool Bool.false (nat_eqb i d) Bool.true
       (Eq.symm Bool (nat_eqb i d) Bool.false h)
       (Eq.trans Bool (nat_eqb i d) (nat_eqb i i) Bool.true
         (Eq.cong Nat Bool (fun (j : Nat) => nat_eqb i j) d i
           (Eq.symm Nat i d (nat_sub_eq_zero_antisymm i d hi hd)))
         (nat_eqb_refl i))))
   (fun (k : Nat) (hi : Eq Nat (Nat.sub i d) (Nat.succ k)) =>
     Eq.trans KExpr (instantiate_bvar_at i d p) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))
       (instantiate_bvar_at i d q)
       (instantiate_bvar_at_above i d p hd
         (Eq.trans Nat (Nat.sub i d) (Nat.succ k)
           (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) hi
           (Eq.cong Nat Nat (fun (n : Nat) => Nat.succ (Nat.sub n (Nat.succ Nat.zero)))
             (Nat.succ k) (Nat.sub i d) (Eq.symm Nat (Nat.sub i d) (Nat.succ k) hi))))
       (Eq.symm KExpr (instantiate_bvar_at i d q) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))
         (instantiate_bvar_at_above i d q hd
           (Eq.trans Nat (Nat.sub i d) (Nat.succ k)
             (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) hi
             (Eq.cong Nat Nat (fun (n : Nat) => Nat.succ (Nat.sub n (Nat.succ Nat.zero)))
               (Nat.succ k) (Nat.sub i d) (Eq.symm Nat (Nat.sub i d) (Nat.succ k) hi)))))))
 (fun (k : Nat) (hd : Eq Nat (Nat.sub d i) (Nat.succ k)) =>
   Eq.trans KExpr (instantiate_bvar_at i d p) (KExpr.bvar i) (instantiate_bvar_at i d q)
     (instantiate_bvar_at_below i d p
       (Eq.trans Nat (Nat.sub d i) (Nat.succ k)
         (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero))) hd
         (Eq.cong Nat Nat (fun (n : Nat) => Nat.succ (Nat.sub n (Nat.succ Nat.zero)))
           (Nat.succ k) (Nat.sub d i) (Eq.symm Nat (Nat.sub d i) (Nat.succ k) hd))))
     (Eq.symm KExpr (instantiate_bvar_at i d q) (KExpr.bvar i)
       (instantiate_bvar_at_below i d q
         (Eq.trans Nat (Nat.sub d i) (Nat.succ k)
           (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero))) hd
           (Eq.cong Nat Nat (fun (n : Nat) => Nat.succ (Nat.sub n (Nat.succ Nat.zero)))
             (Nat.succ k) (Nat.sub d i) (Eq.symm Nat (Nat.sub d i) (Nat.succ k) hd))))))",
    ),
    (
        "instantiate_at_absent_independent",
        r"forall (e : KExpr) (d : Nat) (p : KExpr) (q : KExpr),
 Eq Bool (occurs_in d e) Bool.false ->
 Eq KExpr (instantiate_at e p d) (instantiate_at e q d)",
        r"fun (e : KExpr) => KExpr.rec
 (fun (e0 : KExpr) => forall (d : Nat) (p : KExpr) (q : KExpr),
   Eq Bool (occurs_in d e0) Bool.false -> Eq KExpr (instantiate_at e0 p d) (instantiate_at e0 q d))
 (fun (u : Level) (d : Nat) (p : KExpr) (q : KExpr)
   (_h : Eq Bool (occurs_in d (KExpr.sort u)) Bool.false) => Eq.refl KExpr (KExpr.sort u))
 (fun (i : Nat) (d : Nat) (p : KExpr) (q : KExpr)
   (h : Eq Bool (occurs_in d (KExpr.bvar i)) Bool.false) => projection_absent_bvar i d p q h)
 (fun (f : KExpr) (a : KExpr)
   (ihf : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d f) Bool.false -> Eq KExpr (instantiate_at f p d) (instantiate_at f q d))
   (iha : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d a) Bool.false -> Eq KExpr (instantiate_at a p d) (instantiate_at a q d))
   (d : Nat) (p : KExpr) (q : KExpr) (h : Eq Bool (occurs_in d (KExpr.app f a)) Bool.false) =>
   universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.app x y)
     (instantiate_at f p d) (instantiate_at f q d) (instantiate_at a p d) (instantiate_at a q d)
     (ihf d p q (projection_absent_or_left (occurs_in d f) (occurs_in d a) h))
     (iha d p q (projection_absent_or_right (occurs_in d f) (occurs_in d a) h)))
 (fun (A : KExpr) (b : KExpr)
   (ihA : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d A) Bool.false -> Eq KExpr (instantiate_at A p d) (instantiate_at A q d))
   (ihb : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d b) Bool.false -> Eq KExpr (instantiate_at b p d) (instantiate_at b q d))
   (d : Nat) (p : KExpr) (q : KExpr) (h : Eq Bool (occurs_in d (KExpr.lam A b)) Bool.false) =>
   universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.lam x y)
     (instantiate_at A p d) (instantiate_at A q d)
     (instantiate_at b p (Nat.succ d)) (instantiate_at b q (Nat.succ d))
     (ihA d p q (projection_absent_or_left (occurs_in d A) (occurs_in (Nat.succ d) b) h))
     (ihb (Nat.succ d) p q (projection_absent_or_right (occurs_in d A) (occurs_in (Nat.succ d) b) h)))
 (fun (A : KExpr) (B : KExpr)
   (ihA : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d A) Bool.false -> Eq KExpr (instantiate_at A p d) (instantiate_at A q d))
   (ihB : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d B) Bool.false -> Eq KExpr (instantiate_at B p d) (instantiate_at B q d))
   (d : Nat) (p : KExpr) (q : KExpr) (h : Eq Bool (occurs_in d (KExpr.pi A B)) Bool.false) =>
   universe_bridge_congr2 KExpr KExpr KExpr (fun (x : KExpr) (y : KExpr) => KExpr.pi x y)
     (instantiate_at A p d) (instantiate_at A q d)
     (instantiate_at B p (Nat.succ d)) (instantiate_at B q (Nat.succ d))
     (ihA d p q (projection_absent_or_left (occurs_in d A) (occurs_in (Nat.succ d) B) h))
     (ihB (Nat.succ d) p q (projection_absent_or_right (occurs_in d A) (occurs_in (Nat.succ d) B) h)))
 (fun (n : Name) (us : ListType Level) (d : Nat) (p : KExpr) (q : KExpr)
   (_h : Eq Bool (occurs_in d (KExpr.const n us)) Bool.false) => Eq.refl KExpr (KExpr.const n us))
 (fun (A : KExpr) (v : KExpr) (b : KExpr)
   (ihA : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d A) Bool.false -> Eq KExpr (instantiate_at A p d) (instantiate_at A q d))
   (ihv : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d v) Bool.false -> Eq KExpr (instantiate_at v p d) (instantiate_at v q d))
   (ihb : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d b) Bool.false -> Eq KExpr (instantiate_at b p d) (instantiate_at b q d))
   (d : Nat) (p : KExpr) (q : KExpr) (h : Eq Bool (occurs_in d (KExpr.let_ A v b)) Bool.false) =>
   psubst_closed_cong3 (fun (x : KExpr) (y : KExpr) (z : KExpr) => KExpr.let_ x y z)
     (instantiate_at A p d) (instantiate_at A q d) (instantiate_at v p d) (instantiate_at v q d)
     (instantiate_at b p (Nat.succ d)) (instantiate_at b q (Nat.succ d))
     (ihA d p q (projection_absent_or_left (occurs_in d A)
       (Bool.or (occurs_in d v) (occurs_in (Nat.succ d) b)) h))
     (ihv d p q (projection_absent_or_left (occurs_in d v) (occurs_in (Nat.succ d) b)
       (projection_absent_or_right (occurs_in d A) (Bool.or (occurs_in d v) (occurs_in (Nat.succ d) b)) h)))
     (ihb (Nat.succ d) p q (projection_absent_or_right (occurs_in d v) (occurs_in (Nat.succ d) b)
       (projection_absent_or_right (occurs_in d A) (Bool.or (occurs_in d v) (occurs_in (Nat.succ d) b)) h))))
 (fun (S : Name) (i : Nat) (sub : KExpr)
   (ih : forall (d : Nat) (p : KExpr) (q : KExpr), Eq Bool (occurs_in d sub) Bool.false -> Eq KExpr (instantiate_at sub p d) (instantiate_at sub q d))
   (d : Nat) (p : KExpr) (q : KExpr) (h : Eq Bool (occurs_in d (KExpr.proj S i sub)) Bool.false) =>
   Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj S i x)
     (instantiate_at sub p d) (instantiate_at sub q d) (ih d p q h))
 (fun (n : Nat) (d : Nat) (p : KExpr) (q : KExpr)
   (_h : Eq Bool (occurs_in d (KExpr.lit n)) Bool.false) => Eq.refl KExpr (KExpr.lit n)) e",
    ),
    (
        "instantiate_absent_independent",
        r"forall (B : KExpr) (p : KExpr) (q : KExpr), Eq Bool (occurs_in Nat.zero B) Bool.false ->
 Eq KExpr (instantiate B p) (instantiate B q)",
        r"fun (B : KExpr) (p : KExpr) (q : KExpr) => instantiate_at_absent_independent B Nat.zero p q",
    ),
    (
        "projection_field_body_unused_binder",
        r"forall (B : KExpr) (S : Name) (i : Nat) (e : KExpr) (dummy : KExpr),
 Eq Bool (occurs_in Nat.zero B) Bool.false ->
 Eq KExpr (projection_field_body B (KExpr.proj S i e)) (instantiate B dummy)",
        r"fun (B : KExpr) (S : Name) (i : Nat) (e : KExpr) (dummy : KExpr)
 (h : Eq Bool (occurs_in Nat.zero B) Bool.false) =>
 Eq.trans KExpr (projection_field_body B (KExpr.proj S i e)) (instantiate B (KExpr.proj S i e))
   (instantiate B dummy) (projection_field_body_eq_instantiate B (KExpr.proj S i e))
   (instantiate_absent_independent B (KExpr.proj S i e) dummy h)",
    ),
    (
        "projection_unused_outer_bvar",
        r"forall (S : Name) (i : Nat) (e : KExpr),
 Eq KExpr (projection_field_body (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.proj S i e))
   (KExpr.bvar Nat.zero)",
        r"fun (S : Name) (i : Nat) (e : KExpr) =>
 projection_field_body_unused_binder (KExpr.bvar (Nat.succ Nat.zero)) S i e
   (KExpr.sort Level.zero) (Eq.refl Bool Bool.false)",
    ),
    (
        "projection_unused_outer_not_closed",
        r"Eq Bool (closed_at_b (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_unused_nested_lambda",
        r"forall (S : Name) (i : Nat) (e : KExpr),
 Eq KExpr (projection_field_body
   (KExpr.lam (KExpr.sort Level.zero)
     (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))
   (KExpr.proj S i e))
   (KExpr.lam (KExpr.sort Level.zero)
     (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))))",
        r"fun (S : Name) (i : Nat) (e : KExpr) =>
 projection_field_body_unused_binder
   (KExpr.lam (KExpr.sort Level.zero)
     (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))
   S i e (KExpr.sort Level.zero) (Eq.refl Bool Bool.false)",
    ),
    (
        "projection_unused_nested_pi_let",
        r"forall (S : Name) (i : Nat) (e : KExpr),
 Eq KExpr (projection_field_body
   (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero))
     (KExpr.let_ (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
       (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
       (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
   (KExpr.proj S i e))
   (KExpr.pi (KExpr.bvar Nat.zero)
     (KExpr.let_ (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))
       (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))))",
        r"fun (S : Name) (i : Nat) (e : KExpr) =>
 projection_field_body_unused_binder
   (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero))
     (KExpr.let_ (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
       (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
       (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
   S i e (KExpr.sort Level.zero) (Eq.refl Bool Bool.false)",
    ),
    (
        "projection_live_binder_independence_false",
        r"forall (h : Eq KExpr
 (instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))
 (instantiate (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))), Empty",
        r"fun (h : Eq KExpr
 (instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))
 (instantiate (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))) =>
 kexpr_discr_t Empty (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) h (Eq.refl Bool Bool.false)",
    ),
    (
        "projection_nested_live_binder_present",
        r"Eq Bool (occurs_in Nat.zero
 (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_occurs_bound_lam_absent",
        r"Eq Bool (occurs_in Nat.zero (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_occurs_bound_pi_absent",
        r"Eq Bool (occurs_in Nat.zero (KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_occurs_outer_pi_present",
        r"Eq Bool (occurs_in Nat.zero (KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_occurs_bound_let_absent",
        r"Eq Bool (occurs_in Nat.zero (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_occurs_outer_let_present",
        r"Eq Bool (occurs_in Nat.zero (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_positivity_nested_self_refused",
        r"Eq Bool (strictly_positive_in Nat.zero
 (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_positivity_bound_domain_allowed",
        r"Eq Bool (strictly_positive_in Nat.zero
 (KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_ctor_nested_self_refused",
        r"Eq Bool (ctor_positive Nat.zero
 (KExpr.pi (KExpr.sort Level.zero)
   (KExpr.pi (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero))
     (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_ctor_bound_domain_allowed",
        r"Eq Bool (ctor_positive Nat.zero
 (KExpr.pi (KExpr.sort Level.zero)
   (KExpr.pi (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))
     (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_ctor_list_nested_self_refused",
        r"Eq Bool (strictly_positive_ctors_b
 (CtorDecls.cons (CtorDecl.mk Nat.zero
   (KExpr.pi (KExpr.sort Level.zero)
     (KExpr.pi (KExpr.pi (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero))
       (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))) CtorDecls.nil)) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_ctor_list_bound_domain_allowed",
        r"Eq Bool (strictly_positive_ctors_b
 (CtorDecls.cons (CtorDecl.mk Nat.zero
   (KExpr.pi (KExpr.sort Level.zero)
     (KExpr.pi (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))
       (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))) CtorDecls.nil)) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_return_one_parameter_allowed",
        r"Eq Bool (return_args_wf_from (Nat.succ Nat.zero) (Nat.succ Nat.zero)
 (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_return_two_parameters_allowed",
        r"Eq Bool (return_args_wf_from (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))
 (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)))
   (KExpr.bvar Nat.zero))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_return_swapped_parameters_refused",
        r"Eq Bool (return_args_wf_from (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))
 (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))
   (KExpr.bvar (Nat.succ Nat.zero)))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_return_missing_parameter_refused",
        r"Eq Bool (return_args_wf_from (Nat.succ Nat.zero) (Nat.succ Nat.zero)
 (KExpr.bvar (Nat.succ Nat.zero))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    (
        "projection_ctor_parameter_return_allowed",
        r"Eq Bool (ctor_return_wf_b (Nat.succ Nat.zero)
 (KExpr.pi (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
    (
        "projection_ctor_list_parameter_return_allowed",
        r"Eq Bool (ctor_decls_wf_b (Nat.succ Nat.zero)
 (CtorDecls.cons (CtorDecl.mk Nat.zero
   (KExpr.pi (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))))
   CtorDecls.nil)) Bool.true",
        r"Eq.refl Bool Bool.true",
    ),
];

impl Specification {
    pub(super) fn add_projection_unused_binder(&mut self) -> Result<(), SpecError> {
        for &(name, type_src, value_src) in PROOFS {
            super::acceptance_in::theorem(
                self,
                name,
                type_src,
                value_src,
                "Absent-index substitution independence and its actual projection-field-body consumer. Arbitrary expressions and outer bound variables; no closedness or output-typing premise.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name};

    #[test]
    fn projection_unused_binder_proof_records_parse() {
        assert_eq!(PROOFS.len(), 30);
        for &(name, type_src, value_src) in PROOFS {
            clean_parser::parse_decl(&format!("def {name} : {type_src} := {value_src}"))
                .expect("explicit checked theorem record parses");
        }
    }

    #[test]
    fn projection_unused_binder_actual_proofs_recheck_without_axioms() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for &(name, type_src, value_src) in PROOFS {
                let definition = spec.definitions().get(name).expect("registered proof");
                let kernel_name = Name::from_string(name);
                let constant = spec.env().get_const(&kernel_name).expect("actual root");
                let ty = definition.elaborated_type.as_ref().expect("checked type");
                let value = definition.elaborated_value.as_ref().expect("checked body");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{name}"
                );
                assert_eq!(definition.type_src, type_src, "{name}");
                assert_eq!(definition.value_src.as_deref(), Some(value_src), "{name}");
                assert_eq!(&constant.type_, ty, "{name}");
                assert_eq!(constant.value.as_ref(), Some(value), "{name}");
                assert!(
                    !matches!(value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                    "{name}"
                );
                spec.verify_definition(name).expect("actual proof rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&kernel_name)
                        .expect("domain closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("foundation closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn projection_unused_binder_rejects_live_and_unlowered_forgeries() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                r"def projection_forged_live_absence : Eq Bool (occurs_in Nat.zero (KExpr.bvar Nat.zero)) Bool.false := Eq.refl Bool Bool.false",
                r"def projection_forged_nested_absence : Eq Bool (occurs_in Nat.zero (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))) Bool.false := Eq.refl Bool Bool.false",
                r"def projection_forged_outer_unchanged : Eq KExpr (projection_field_body (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))) (KExpr.bvar (Nat.succ Nat.zero)) := Eq.refl KExpr (KExpr.bvar (Nat.succ Nat.zero))",
                r"def projection_forged_live_independence : Eq KExpr (instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (instantiate (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) := instantiate_absent_independent (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (Eq.refl Bool Bool.false)",
            ] {
                let clean_parser::SurfaceDecl::Def { name, .. } =
                    clean_parser::parse_decl(source).expect("negative control must parse")
                else {
                    panic!("expected a definition");
                };
                let error = spec
                    .add_recursive_def(source, "Well-formed negative unused-binder control.")
                    .expect_err("live replacement or unlowered outer variable must be refused");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                // Legacy record-key projection only; exact kernel identity is checked separately.
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .get_const(&name.qualify_under(&Default::default()).into_name())
                        .is_none(),
                    "{name}"
                );
            }
        });
    }
}
