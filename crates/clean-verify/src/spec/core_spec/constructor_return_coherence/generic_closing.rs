// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generic monomorphic self-closing of admitted constructor signatures.
//!
//! Closing by a constant preserves telescope length and returns; the actual
//! modeled admission derives the bound that keeps parameters below the self
//! reference. The chosen Name is not a general representation of numeric IDs.
//! Indexed admission, universe instantiation and Rust execution remain separate.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "gcc_named_return_spine",
        r"forall (n : Name) (d np : Nat), KExpr",
        r"fun (n : Name) (d np : Nat) => Nat.rec (fun (_p : Nat) => KExpr) (KExpr.const n (ListType.nil Level))
 (fun (p : Nat) (f : KExpr) => KExpr.app f (KExpr.bvar (Nat.sub d (Nat.succ p)))) np",
    ),
    DeclarationInput::Proof(
        "gcc_sub_le",
        r"forall (d p : Nat), Le (Nat.sub d p) d",
        r"fun (d : Nat) => Nat.rec (fun (d0 : Nat) => forall (p : Nat), Le (Nat.sub d0 p) d0)
 (fun (p : Nat) => Eq.subst Nat (fun (x : Nat) => Le x Nat.zero)
  Nat.zero (Nat.sub Nat.zero p) (Eq.symm Nat (Nat.sub Nat.zero p) Nat.zero (nat_sub_zero_left p)) (Le.refl Nat.zero))
 (fun (d0 : Nat) (ih : forall (p : Nat), Le (Nat.sub d0 p) d0) (p : Nat) =>
  Nat.rec (fun (p0 : Nat) => Le (Nat.sub (Nat.succ d0) p0) (Nat.succ d0))
   (Le.refl (Nat.succ d0))
   (fun (p0 : Nat) (_prev : Le (Nat.sub (Nat.succ d0) p0) (Nat.succ d0)) =>
    Eq.subst Nat (fun (x : Nat) => Le x (Nat.succ d0))
     (Nat.sub d0 p0) (Nat.sub (Nat.succ d0) (Nat.succ p0))
     (Eq.symm Nat (Nat.sub (Nat.succ d0) (Nat.succ p0)) (Nat.sub d0 p0) (nat_sub_succ_succ d0 p0))
     (Le.step (Nat.sub d0 p0) d0 (ih p0))) p) d",
    ),
    DeclarationInput::Proof(
        "gcc_slot_below",
        r"forall (d p : Nat), Le (Nat.succ p) d -> Le (Nat.succ (Nat.sub d (Nat.succ p))) d",
        r"fun (d : Nat) => Nat.rec
 (fun (d0 : Nat) => forall (p : Nat), Le (Nat.succ p) d0 -> Le (Nat.succ (Nat.sub d0 (Nat.succ p))) d0)
 (fun (p : Nat) (h : Le (Nat.succ p) Nat.zero) =>
  nat_zero_ne_succ_prop p (Le (Nat.succ (Nat.sub Nat.zero (Nat.succ p))) Nat.zero)
   (Eq.symm Nat (Nat.succ p) Nat.zero (le_zero_eq_zero (Nat.succ p) Nat.zero h (Eq.refl Nat Nat.zero))))
 (fun (d0 : Nat)
  (_ih : forall (p : Nat), Le (Nat.succ p) d0 -> Le (Nat.succ (Nat.sub d0 (Nat.succ p))) d0)
  (p : Nat) (_h : Le (Nat.succ p) (Nat.succ d0)) =>
   Eq.subst Nat (fun (x : Nat) => Le (Nat.succ x) (Nat.succ d0))
    (Nat.sub d0 p) (Nat.sub (Nat.succ d0) (Nat.succ p))
    (Eq.symm Nat (Nat.sub (Nat.succ d0) (Nat.succ p)) (Nat.sub d0 p) (nat_sub_succ_succ d0 p))
    (le_succ_succ (Nat.sub d0 p) d0 (gcc_sub_le d0 p))) d",
    ),
    DeclarationInput::Proof(
        "gcc_close_self_bvar",
        r"forall (n : Name) (d : Nat), Eq KExpr (instantiate_at (KExpr.bvar d) (KExpr.const n (ListType.nil Level)) d) (KExpr.const n (ListType.nil Level))",
        r"fun (n : Name) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.bvar d) (KExpr.const n (ListType.nil Level)) d)
 (instantiate_bvar_at d d (KExpr.const n (ListType.nil Level))) (KExpr.const n (ListType.nil Level))
 (instantiate_at_bvar d (KExpr.const n (ListType.nil Level)) d)
 (Eq.trans KExpr (instantiate_bvar_at d d (KExpr.const n (ListType.nil Level))) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero d) (KExpr.const n (ListType.nil Level))
  (instantiate_bvar_at_eq d (KExpr.const n (ListType.nil Level))) (lift_at_const n (ListType.nil Level) Nat.zero d))",
    ),
    DeclarationInput::Proof(
        "gcc_close_parameter_bvar",
        r"forall (n : Name) (d p : Nat), Le (Nat.succ p) d -> Eq KExpr (instantiate_at (KExpr.bvar (Nat.sub d (Nat.succ p))) (KExpr.const n (ListType.nil Level)) d) (KExpr.bvar (Nat.sub d (Nat.succ p)))",
        r"fun (n : Name) (d p : Nat) (h : Le (Nat.succ p) d) =>
 Eq.trans KExpr (instantiate_at (KExpr.bvar (Nat.sub d (Nat.succ p))) (KExpr.const n (ListType.nil Level)) d)
  (instantiate_bvar_at (Nat.sub d (Nat.succ p)) d (KExpr.const n (ListType.nil Level))) (KExpr.bvar (Nat.sub d (Nat.succ p)))
  (instantiate_at_bvar (Nat.sub d (Nat.succ p)) (KExpr.const n (ListType.nil Level)) d)
  (inst_bvar_lt (Nat.sub d (Nat.succ p)) d (KExpr.const n (ListType.nil Level)) (gcc_slot_below d p h))",
    ),
    DeclarationInput::Proof(
        "gcc_bvar_const_count",
        r"forall (n : Name) (i k : Nat), Eq Nat (count_pi (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) k)) Nat.zero",
        r"fun (n : Name) (i k : Nat) => Nat.rec
 (fun (q : Nat) => Eq Nat (count_pi (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q)) Nat.zero)
 (Nat.rec (fun (q : Nat) => Eq Nat (count_pi (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q)) Nat.zero)
  (Eq.refl Nat Nat.zero)
  (fun (q : Nat) (_ih : Eq Nat (count_pi (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q)) Nat.zero) => Eq.refl Nat Nat.zero) (Nat.sub i k))
 (fun (q : Nat) (_ih : Eq Nat (count_pi (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q)) Nat.zero) => Eq.refl Nat Nat.zero) (Nat.sub k i)",
    ),
    DeclarationInput::Proof(
        "gcc_bvar_const_return",
        r"forall (n : Name) (i k : Nat), Eq KExpr (return_type (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) k)",
        r"fun (n : Name) (i k : Nat) => Nat.rec
 (fun (q : Nat) => Eq KExpr (return_type (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q)) (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q))
 (Nat.rec (fun (q : Nat) => Eq KExpr (return_type (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q)) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q))
  (Eq.refl KExpr (KExpr.const n (ListType.nil Level)))
  (fun (q : Nat) (_ih : Eq KExpr (return_type (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q)) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) q)) => Eq.refl KExpr (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))) (Nat.sub i k))
 (fun (q : Nat) (_ih : Eq KExpr (return_type (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q)) (Nat.rec (fun (_q : Nat) => KExpr) (Nat.rec (fun (_q : Nat) => KExpr) (lift_at (KExpr.const n (ListType.nil Level)) Nat.zero k)
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Nat.sub i k))
 (fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) q)) => Eq.refl KExpr (KExpr.bvar i)) (Nat.sub k i)",
    ),
    DeclarationInput::Proof(
        "gcc_count_pi_close_const",
        r"forall (ct : KExpr) (n : Name) (k : Nat), Eq Nat (count_pi (instantiate_at ct (KExpr.const n (ListType.nil Level)) k)) (count_pi ct)",
        r"fun (ct : KExpr) (n : Name) => KExpr.rec (fun (e : KExpr) => forall (k : Nat), Eq Nat (count_pi (instantiate_at e (KExpr.const n (ListType.nil Level)) k)) (count_pi e))
 (fun (u : Level) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (i : Nat) (k : Nat) => gcc_bvar_const_count n i k)
 (fun (f : KExpr) (a : KExpr) (ih_f : forall (k : Nat), Eq Nat (count_pi (instantiate_at f (KExpr.const n (ListType.nil Level)) k)) (count_pi f)) (ih_a : forall (k : Nat), Eq Nat (count_pi (instantiate_at a (KExpr.const n (ListType.nil Level)) k)) (count_pi a)) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (b : KExpr) (ih_A : forall (k : Nat), Eq Nat (count_pi (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (count_pi A)) (ih_b : forall (k : Nat), Eq Nat (count_pi (instantiate_at b (KExpr.const n (ListType.nil Level)) k)) (count_pi b)) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (B : KExpr) (ih_A : forall (k : Nat), Eq Nat (count_pi (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (count_pi A)) (ih_B : forall (k : Nat), Eq Nat (count_pi (instantiate_at B (KExpr.const n (ListType.nil Level)) k)) (count_pi B)) (k : Nat) => Eq.cong Nat Nat Nat.succ (count_pi (instantiate_at B (KExpr.const n (ListType.nil Level)) (Nat.succ k))) (count_pi B) (ih_B (Nat.succ k)))
 (fun (nm : Name) (us : ListType Level) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : forall (k : Nat), Eq Nat (count_pi (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (count_pi A)) (ih_v : forall (k : Nat), Eq Nat (count_pi (instantiate_at v (KExpr.const n (ListType.nil Level)) k)) (count_pi v)) (ih_b : forall (k : Nat), Eq Nat (count_pi (instantiate_at b (KExpr.const n (ListType.nil Level)) k)) (count_pi b)) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (S : Name) (i : Nat) (subject : KExpr) (ih_subject : forall (k : Nat), Eq Nat (count_pi (instantiate_at subject (KExpr.const n (ListType.nil Level)) k)) (count_pi subject)) (k : Nat) => Eq.refl Nat Nat.zero)
 (fun (i : Nat) (k : Nat) => Eq.refl Nat Nat.zero) ct",
    ),
    DeclarationInput::Proof(
        "gcc_add_succ_transfer",
        r"forall (a k : Nat), Eq Nat (Nat.add a (Nat.succ k)) (Nat.add (Nat.succ a) k)",
        r"fun (a k : Nat) => Eq.trans Nat (Nat.add a (Nat.succ k)) (Nat.add (Nat.succ k) a) (Nat.add (Nat.succ a) k)
 (nat_add_comm a (Nat.succ k))
 (Eq.trans Nat (Nat.add (Nat.succ k) a) (Nat.succ (Nat.add k a)) (Nat.add (Nat.succ a) k)
  (Eq.trans Nat (Nat.add (Nat.succ k) a) (Nat.add a (Nat.succ k)) (Nat.succ (Nat.add k a))
   (nat_add_comm (Nat.succ k) a)
   (Eq.trans Nat (Nat.add a (Nat.succ k)) (Nat.succ (Nat.add a k)) (Nat.succ (Nat.add k a))
    (nat_add_succ_right a k) (Eq.cong Nat Nat Nat.succ (Nat.add a k) (Nat.add k a) (nat_add_comm a k))))
  (Eq.trans Nat (Nat.succ (Nat.add k a)) (Nat.add k (Nat.succ a)) (Nat.add (Nat.succ a) k)
   (Eq.symm Nat (Nat.add k (Nat.succ a)) (Nat.succ (Nat.add k a)) (nat_add_succ_right k a))
   (nat_add_comm k (Nat.succ a))))",
    ),
    DeclarationInput::Proof(
        "gcc_return_type_close_const",
        r"forall (ct : KExpr) (n : Name) (k : Nat), Eq KExpr (return_type (instantiate_at ct (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi ct) k))",
        r"fun (ct : KExpr) (n : Name) => KExpr.rec (fun (e : KExpr) => forall (k : Nat), Eq KExpr (return_type (instantiate_at e (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type e) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi e) k)))
 (fun (u : Level) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.sort u) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (i : Nat) (k : Nat) => Eq.trans KExpr (return_type (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) k) (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) (Nat.add Nat.zero k))
 (gcc_bvar_const_return n i k) (Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.bvar i) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k))))
 (fun (f : KExpr) (a : KExpr) (ih_f : forall (k : Nat), Eq KExpr (return_type (instantiate_at f (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type f) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi f) k))) (ih_a : forall (k : Nat), Eq KExpr (return_type (instantiate_at a (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type a) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi a) k))) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.app f a) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (A : KExpr) (b : KExpr) (ih_A : forall (k : Nat), Eq KExpr (return_type (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type A) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi A) k))) (ih_b : forall (k : Nat), Eq KExpr (return_type (instantiate_at b (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type b) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi b) k))) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.lam A b) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (A : KExpr) (B : KExpr) (ih_A : forall (k : Nat), Eq KExpr (return_type (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type A) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi A) k))) (ih_B : forall (k : Nat), Eq KExpr (return_type (instantiate_at B (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type B) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi B) k))) (k : Nat) => Eq.trans KExpr (return_type (instantiate_at B (KExpr.const n (ListType.nil Level)) (Nat.succ k)))
 (instantiate_at (return_type B) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi B) (Nat.succ k)))
 (instantiate_at (return_type B) (KExpr.const n (ListType.nil Level)) (Nat.add (Nat.succ (count_pi B)) k))
 (ih_B (Nat.succ k))
 (Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (return_type B) (KExpr.const n (ListType.nil Level)) q))
  (Nat.add (count_pi B) (Nat.succ k)) (Nat.add (Nat.succ (count_pi B)) k) (gcc_add_succ_transfer (count_pi B) k)))
 (fun (nm : Name) (us : ListType Level) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.const nm us) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : forall (k : Nat), Eq KExpr (return_type (instantiate_at A (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type A) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi A) k))) (ih_v : forall (k : Nat), Eq KExpr (return_type (instantiate_at v (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type v) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi v) k))) (ih_b : forall (k : Nat), Eq KExpr (return_type (instantiate_at b (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type b) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi b) k))) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.let_ A v b) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (S : Name) (i : Nat) (subject : KExpr) (ih_subject : forall (k : Nat), Eq KExpr (return_type (instantiate_at subject (KExpr.const n (ListType.nil Level)) k)) (instantiate_at (return_type subject) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi subject) k))) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.proj S i subject) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k)))
 (fun (i : Nat) (k : Nat) => Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (KExpr.lit i) (KExpr.const n (ListType.nil Level)) q)) k (Nat.add Nat.zero k)
 (Eq.symm Nat (Nat.add Nat.zero k) k (nat_add_zero k))) ct",
    ),
    DeclarationInput::Proof(
        "gcc_return_type_close_self",
        r"forall (ct : KExpr) (n : Name), Eq KExpr (return_type (instantiate ct (KExpr.const n (ListType.nil Level)))) (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (count_pi ct))",
        r"fun (ct : KExpr) (n : Name) => Eq.trans KExpr (return_type (instantiate ct (KExpr.const n (ListType.nil Level))))
 (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (Nat.add (count_pi ct) Nat.zero)) (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (count_pi ct))
 (gcc_return_type_close_const ct n Nat.zero)
 (Eq.cong Nat KExpr (fun (q : Nat) => (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) q))
  (Nat.add (count_pi ct) Nat.zero) (count_pi ct) (nat_add_zero_right (count_pi ct)))",
    ),
    DeclarationInput::Proof(
        "gcc_close_return_spine",
        r"forall (n : Name) (d np : Nat), Le np d -> Eq KExpr (instantiate_at (arc_return_spine d np) (KExpr.const n (ListType.nil Level)) d) (gcc_named_return_spine n d np)",
        r"fun (n : Name) (d np : Nat) => Nat.rec
 (fun (p : Nat) => Le p d -> Eq KExpr (instantiate_at (arc_return_spine d p) (KExpr.const n (ListType.nil Level)) d) (gcc_named_return_spine n d p))
 (fun (_h : Le Nat.zero d) => gcc_close_self_bvar n d)
 (fun (p : Nat)
  (ih : Le p d -> Eq KExpr (instantiate_at (arc_return_spine d p) (KExpr.const n (ListType.nil Level)) d) (gcc_named_return_spine n d p))
  (h : Le (Nat.succ p) d) =>
  universe_bridge_congr2 KExpr KExpr KExpr KExpr.app
   (instantiate_at (arc_return_spine d p) (KExpr.const n (ListType.nil Level)) d) (gcc_named_return_spine n d p)
   (instantiate_at (KExpr.bvar (Nat.sub d (Nat.succ p))) (KExpr.const n (ListType.nil Level)) d) (KExpr.bvar (Nat.sub d (Nat.succ p)))
   (ih (le_trans p (Nat.succ p) d (Le.step p p (Le.refl p)) h))
   (gcc_close_parameter_bvar n d p h)) np",
    ),
    DeclarationInput::Proof(
        "gcc_admitted_return_named",
        r"forall (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls) (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr) (found : Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (OptionType.some CtorDecl (CtorDecl.mk id ct))) (n : Name), Eq KExpr (return_type (instantiate ct (KExpr.const n (ListType.nil Level)))) (gcc_named_return_spine n (count_pi ct) np)",
        r"fun (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls) (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr) (found : Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (OptionType.some CtorDecl (CtorDecl.mk id ct))) (n : Name) => Eq.trans KExpr (return_type (instantiate ct (KExpr.const n (ListType.nil Level))))
 (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (count_pi ct)) (gcc_named_return_spine n (count_pi ct) np)
 (gcc_return_type_close_self ct n)
 (Eq.trans KExpr (instantiate_at (return_type ct) (KExpr.const n (ListType.nil Level)) (count_pi ct))
  (instantiate_at (arc_return_spine (count_pi ct) np) (KExpr.const n (ListType.nil Level)) (count_pi ct)) (gcc_named_return_spine n (count_pi ct) np)
  (Eq.cong KExpr KExpr (fun (e : KExpr) => (instantiate_at e (KExpr.const n (ListType.nil Level)) (count_pi ct)))
   (return_type ct) (arc_return_spine (count_pi ct) np) (arc_admitted_selected_spine env family np ty ctors wf i id ct found))
  (gcc_close_return_spine n (count_pi ct) np (arc_admitted_selected_arity env family np ty ctors wf i id ct found)))",
    ),
    DeclarationInput::Proof(
        "gcc_admitted_closed_arity",
        r"forall (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls) (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr) (found : Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (OptionType.some CtorDecl (CtorDecl.mk id ct))) (n : Name), Le np (count_pi (instantiate ct (KExpr.const n (ListType.nil Level))))",
        r"fun (env : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls) (wf : WellFormedCtorDecls env family np ty ctors) (i id : Nat) (ct : KExpr) (found : Eq (OptionType CtorDecl) (ac_ctor_at ctors i) (OptionType.some CtorDecl (CtorDecl.mk id ct))) (n : Name) => Eq.subst Nat (fun (d : Nat) => Le np d)
 (count_pi ct) (count_pi (instantiate ct (KExpr.const n (ListType.nil Level))))
 (Eq.symm Nat (count_pi (instantiate ct (KExpr.const n (ListType.nil Level)))) (count_pi ct) (gcc_count_pi_close_const ct n Nat.zero))
 (arc_admitted_selected_arity env family np ty ctors wf i id ct found)",
    ),
    DeclarationInput::Proof(
        "gcc_prod_admitted_named",
        r"Eq KExpr (return_type (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)))) (gcc_named_return_spine (rpa_source_name Nat.zero) rpa_four rpa_two)",
        r"gcc_admitted_return_named KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_well_formed Nat.zero rpa_one rpa_ctor_ty (Eq.refl (OptionType CtorDecl) (OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty))) (rpa_source_name Nat.zero)",
    ),
    DeclarationInput::Proof(
        "gcc_prod_source_named",
        r"Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (gcc_named_return_spine (rpa_source_name Nat.zero) rpa_four rpa_two)",
        r"Eq.trans KExpr (return_type (kconst_type kcre_prod_mk_signature))
 (return_type (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)))) (gcc_named_return_spine (rpa_source_name Nat.zero) rpa_four rpa_two)
 (Eq.symm KExpr (return_type (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level))))
  (return_type (kconst_type kcre_prod_mk_signature))
  (Eq.cong KExpr KExpr return_type (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level))) (kconst_type kcre_prod_mk_signature) rpa_close_self))
 gcc_prod_admitted_named",
    ),
    DeclarationInput::Proof(
        "gcc_prod_source_slots",
        r"Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))",
        r"gcc_prod_source_named",
    ),
    DeclarationInput::Proof(
        "gcc_prod_source_count",
        r"Eq Nat (count_pi (kconst_type kcre_prod_mk_signature)) rpa_four",
        r"Eq.trans Nat (count_pi (kconst_type kcre_prod_mk_signature))
 (count_pi (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)))) rpa_four
 (Eq.symm Nat (count_pi (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)))) (count_pi (kconst_type kcre_prod_mk_signature))
  (Eq.cong KExpr Nat count_pi (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level))) (kconst_type kcre_prod_mk_signature) rpa_close_self))
 (gcc_count_pi_close_const rpa_ctor_ty (rpa_source_name Nat.zero) Nat.zero)",
    ),
    DeclarationInput::Proof(
        "gcc_prod_closed_arity",
        r"Le rpa_two (count_pi (instantiate rpa_ctor_ty (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level))))",
        r"gcc_admitted_closed_arity KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_well_formed Nat.zero rpa_one rpa_ctor_ty (Eq.refl (OptionType CtorDecl) (OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty))) (rpa_source_name Nat.zero)",
    ),
    DeclarationInput::Proof(
        "gcc_underflow_full_guard_refuses",
        r"Eq Bool (ctor_return_wf_b (Nat.succ Nat.zero) (arc_return_spine Nat.zero (Nat.succ Nat.zero))) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "gcc_underflow_raw_guard_passes",
        r"Eq Bool (return_args_wf_from Nat.zero (Nat.succ Nat.zero) (arc_return_spine Nat.zero (Nat.succ Nat.zero))) Bool.true",
        r"arc_raw_underflow_guard_passes",
    ),
    DeclarationInput::Proof(
        "gcc_underflow_captures_parameter",
        r"forall (n : Name), Eq KExpr (instantiate_at (arc_return_spine Nat.zero (Nat.succ Nat.zero)) (KExpr.const n (ListType.nil Level)) Nat.zero) (KExpr.app (KExpr.const n (ListType.nil Level)) (KExpr.const n (ListType.nil Level)))",
        r"fun (n : Name) => Eq.refl KExpr (KExpr.app (KExpr.const n (ListType.nil Level)) (KExpr.const n (ListType.nil Level)))",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "gcc_forged_wrong_family",
        r"Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name rpa_one) (ListType.nil Level)) (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))",
        r"gcc_prod_source_slots",
    ),
    (
        "gcc_forged_wrong_order",
        r"Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) (KExpr.app (KExpr.app (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)) (KExpr.bvar rpa_two)) (KExpr.bvar rpa_three))",
        r"gcc_prod_source_slots",
    ),
    (
        "gcc_forged_underflow_endpoint",
        r"Eq KExpr (instantiate_at (arc_return_spine Nat.zero (Nat.succ Nat.zero)) (KExpr.const (rpa_source_name Nat.zero) (ListType.nil Level)) Nat.zero) (gcc_named_return_spine (rpa_source_name Nat.zero) Nat.zero (Nat.succ Nat.zero))",
        r"gcc_underflow_captures_parameter (rpa_source_name Nat.zero)",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "gcc_sub_le",
    "gcc_slot_below",
    "gcc_close_self_bvar",
    "gcc_close_parameter_bvar",
    "gcc_bvar_const_count",
    "gcc_bvar_const_return",
    "gcc_count_pi_close_const",
    "gcc_add_succ_transfer",
    "gcc_return_type_close_const",
    "gcc_return_type_close_self",
    "gcc_close_return_spine",
    "gcc_admitted_return_named",
    "gcc_admitted_closed_arity",
    "gcc_prod_admitted_named",
    "gcc_prod_source_named",
    "gcc_prod_source_slots",
    "gcc_prod_source_count",
    "gcc_prod_closed_arity",
    "gcc_underflow_full_guard_refuses",
    "gcc_underflow_raw_guard_passes",
    "gcc_underflow_captures_parameter",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &["gcc_named_return_spine"];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "gcc_sub_le",
    "gcc_slot_below",
    "gcc_close_self_bvar",
    "gcc_close_parameter_bvar",
    "gcc_bvar_const_count",
    "gcc_bvar_const_return",
    "gcc_count_pi_close_const",
    "gcc_add_succ_transfer",
    "gcc_return_type_close_const",
    "gcc_return_type_close_self",
    "gcc_close_return_spine",
    "gcc_admitted_return_named",
    "gcc_admitted_closed_arity",
    "gcc_prod_admitted_named",
    "gcc_prod_source_named",
    "gcc_prod_source_slots",
    "gcc_prod_source_count",
    "gcc_prod_closed_arity",
    "gcc_underflow_full_guard_refuses",
    "gcc_underflow_raw_guard_passes",
    "gcc_underflow_captures_parameter",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[];
