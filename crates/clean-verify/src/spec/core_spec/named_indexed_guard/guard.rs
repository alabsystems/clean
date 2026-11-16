// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "nig_and_intro",
        r"forall (a b : Bool), @Eq Bool a Bool.true -> @Eq Bool b Bool.true -> @Eq Bool (Bool.and a b) Bool.true",
        r"fun (a b : Bool) (ha : @Eq Bool a Bool.true) (hb : @Eq Bool b Bool.true) =>
 Eq.trans Bool (Bool.and a b) (Bool.and Bool.true b) Bool.true
  (Eq.cong Bool Bool (fun (v : Bool) => Bool.and v b) a Bool.true ha) hb",
    ),
    DeclarationInput::Proof(
        "nig_not_true_false",
        r"forall (b : Bool), @Eq Bool (Bool.not b) Bool.true -> @Eq Bool b Bool.false",
        r"fun (b : Bool) => @Bool.rec
 (fun (v : Bool) => @Eq Bool (Bool.not v) Bool.true -> @Eq Bool v Bool.false)
 (fun (_h : @Eq Bool Bool.true Bool.true) => @Eq.refl Bool Bool.false)
 (fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq Bool Bool.true Bool.false) h) b",
    ),
    DeclarationInput::Data(
        "nig_block_free_b",
        r"forall (block : ListType Name) (e : KExpr), Bool",
        r"fun (block : ListType Name) (e : KExpr) =>
 @ListType.rec Name (fun (_ns : ListType Name) => Bool) Bool.true
  (fun (n : Name) (_ns : ListType Name) (ih : Bool) => Bool.and (Bool.not (const_occurs n e)) ih) block",
    ),
    DeclarationInput::Data(
        "nig_indices_free_b",
        r"forall (block : ListType Name) (xs : ListType KExpr), Bool",
        r"fun (block : ListType Name) (xs : ListType KExpr) =>
 @ListType.rec KExpr (fun (_xs : ListType KExpr) => Bool) Bool.true
  (fun (e : KExpr) (_xs : ListType KExpr) (ih : Bool) => Bool.and (nig_block_free_b block e) ih) xs",
    ),
    DeclarationInput::Data(
        "nig_slots",
        r"forall (d p i : Nat), ListType KExpr",
        r"fun (d p : Nat) => @Nat.rec (fun (_p : Nat) => Nat -> ListType KExpr)
 (fun (_i : Nat) => @ListType.nil KExpr)
 (fun (_p : Nat) (ih : Nat -> ListType KExpr) (i : Nat) =>
  @ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i)) (ih (Nat.succ i))) p",
    ),
    DeclarationInput::Data(
        "nig_args_b",
        r"forall (block : ListType Name) (d p i ni : Nat) (xs : ListType KExpr), Bool",
        r"fun (block : ListType Name) (d p i ni : Nat) (xs : ListType KExpr) =>
 @Nat.rec (fun (_p : Nat) => Nat -> ListType KExpr -> Bool)
  (fun (_i : Nat) (ys : ListType KExpr) => Bool.and (nat_eqb (list_length ys) ni) (nig_indices_free_b block ys))
  (fun (_p : Nat) (ih : Nat -> ListType KExpr -> Bool) (j : Nat) (ys : ListType KExpr) =>
   @ListType.rec KExpr (fun (_ys : ListType KExpr) => Bool) Bool.false
    (fun (a : KExpr) (tail : ListType KExpr) (_unused : Bool) =>
     Bool.and (is_bvar_eq (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) j) a) (ih (Nat.succ j) tail)) ys) p i xs",
    ),
    DeclarationInput::Data(
        "nig_head_b",
        r"forall (family : Name) (levels : ListType Level) (e : KExpr), Bool",
        r"fun (family : Name) (levels : ListType Level) (e : KExpr) => @KExpr.rec (fun (_e : KExpr) => Bool)
 (fun (u : Level) => Bool.false)
 (fun (j : Nat) => Bool.false)
 (fun (f : KExpr) (a : KExpr) (ih_f : Bool) (ih_a : Bool) => Bool.false)
 (fun (A : KExpr) (b : KExpr) (ih_A : Bool) (ih_b : Bool) => Bool.false)
 (fun (A : KExpr) (b : KExpr) (ih_A : Bool) (ih_b : Bool) => Bool.false)
 (fun (nm : Name) (us : ListType Level) => Bool.and (name_eqb nm family) (ulist_eqb us levels))
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : Bool) (ih_v : Bool) (ih_b : Bool) => Bool.false)
 (fun (S : Name) (j : Nat) (subject : KExpr) (ih_subject : Bool) => Bool.false)
 (fun (j : Nat) => Bool.false) e",
    ),
    DeclarationInput::Data(
        "nig_strict_app_b",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), Bool",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) =>
 Bool.and (nig_head_b family levels (kapp_fn e)) (nig_args_b block d p Nat.zero ni (kapp_args e))",
    ),
    DeclarationInput::Proof(
        "nig_slots_length",
        r"forall (d p i : Nat), @Eq Nat (list_length (nig_slots d p i)) p",
        r"fun (d p : Nat) => @Nat.rec (fun (p0 : Nat) => forall (i : Nat), @Eq Nat (list_length (nig_slots d p0 i)) p0)
 (fun (_i : Nat) => @Eq.refl Nat Nat.zero)
 (fun (p0 : Nat) (ih : forall (i : Nat), @Eq Nat (list_length (nig_slots d p0 i)) p0) (i : Nat) =>
  Eq.cong Nat Nat Nat.succ (list_length (nig_slots d p0 (Nat.succ i))) p0 (ih (Nat.succ i))) p",
    ),
    DeclarationInput::Proof(
        "nig_args_sound",
        r"forall (block : ListType Name) (d p i ni : Nat) (xs : ListType KExpr), forall (C : Type), @Eq Bool ((nig_args_b block d p i ni xs)) Bool.true -> (forall (ix : ListType KExpr), @Eq (ListType KExpr) xs (list_append (nig_slots d p i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) -> C",
        r"fun (block : ListType Name) (d p i ni : Nat) (xs : ListType KExpr) =>
 @Nat.rec (fun (q : Nat) => forall (i0 : Nat) (ys : ListType KExpr), forall (C : Type), @Eq Bool ((nig_args_b block d q i0 ni ys)) Bool.true -> (forall (ix : ListType KExpr), @Eq (ListType KExpr) ys (list_append (nig_slots d q i0) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) -> C) (fun (i : Nat) (xs : ListType KExpr) (C : Type) (run : @Eq Bool ((nig_args_b block d Nat.zero i ni xs)) Bool.true)
 (k : forall (ix : ListType KExpr), @Eq (ListType KExpr) xs (list_append (nig_slots d Nat.zero i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) =>
 k xs (@Eq.refl (ListType KExpr) xs) (nat_eqb_eq (list_length xs) ni (band_eq_true_left (nat_eqb (list_length xs) ni) (nig_indices_free_b block xs) run)) (band_eq_true_right (nat_eqb (list_length xs) ni) (nig_indices_free_b block xs) run)) (fun (p0 : Nat) (ih : forall (i : Nat) (xs : ListType KExpr), forall (C : Type), @Eq Bool ((nig_args_b block d p0 i ni xs)) Bool.true -> (forall (ix : ListType KExpr), @Eq (ListType KExpr) xs (list_append (nig_slots d p0 i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) -> C) (i : Nat) (xs : ListType KExpr) =>
 @ListType.rec KExpr (fun (ys : ListType KExpr) => forall (C : Type), @Eq Bool ((nig_args_b block d (Nat.succ p0) i ni ys)) Bool.true -> (forall (ix : ListType KExpr), @Eq (ListType KExpr) ys (list_append (nig_slots d (Nat.succ p0) i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) -> C)
 (fun (C : Type) (run : @Eq Bool Bool.false Bool.true)
  (_k : forall (ix : ListType KExpr), @Eq (ListType KExpr) (@ListType.nil KExpr) (list_append (nig_slots d (Nat.succ p0) i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) => bool_false_ne_true_t C run)
 (fun (x : KExpr) (tail : ListType KExpr) (_tail_ih : forall (C : Type), @Eq Bool ((nig_args_b block d (Nat.succ p0) i ni tail)) Bool.true -> (forall (ix : ListType KExpr), @Eq (ListType KExpr) tail (list_append (nig_slots d (Nat.succ p0) i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) -> C) (C : Type)
  (run : @Eq Bool ((nig_args_b block d (Nat.succ p0) i ni (@ListType.cons KExpr x tail))) Bool.true)
  (k : forall (ix : ListType KExpr), @Eq (ListType KExpr) (@ListType.cons KExpr x tail) (list_append (nig_slots d (Nat.succ p0) i) ix) -> @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> C) =>
  ih (Nat.succ i) tail C (band_eq_true_right (is_bvar_eq (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i) x) ((nig_args_b block d p0 (Nat.succ i) ni tail)) run)
   (fun (ix : ListType KExpr) (htail : @Eq (ListType KExpr) tail (list_append (nig_slots d p0 (Nat.succ i)) ix))
    (hlen : @Eq Nat (list_length ix) ni) (hfree : @Eq Bool ((nig_indices_free_b block ix)) Bool.true) => k ix (universe_bridge_congr2 KExpr (ListType KExpr) (ListType KExpr) (fun (element : KExpr) (elements : ListType KExpr) => @ListType.cons KExpr element elements)
 x (KExpr.bvar (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i)) tail (list_append (nig_slots d p0 (Nat.succ i)) ix)
 (arc_is_bvar_eq_sound (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i) x (band_eq_true_left (is_bvar_eq (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i) x) ((nig_args_b block d p0 (Nat.succ i) ni tail)) run)) htail) hlen hfree)) xs) p i xs",
    ),
    DeclarationInput::Proof(
        "nig_args_complete",
        r"forall (block : ListType Name) (d p i ni : Nat), forall (ix : ListType KExpr), @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> @Eq Bool ((nig_args_b block d p i ni (list_append (nig_slots d p i) ix))) Bool.true",
        r"fun (block : ListType Name) (d p i ni : Nat) => @Nat.rec
 (fun (q : Nat) => forall (i0 : Nat), forall (ix : ListType KExpr), @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> @Eq Bool ((nig_args_b block d q i0 ni (list_append (nig_slots d q i0) ix))) Bool.true)
 (fun (i0 : Nat) (ix : ListType KExpr) (hlen : @Eq Nat (list_length ix) ni) (hfree : @Eq Bool ((nig_indices_free_b block ix)) Bool.true) =>
  nig_and_intro (nat_eqb (list_length ix) ni) (nig_indices_free_b block ix)
   (Eq.subst Nat (fun (v : Nat) => @Eq Bool (nat_eqb (list_length ix) v) Bool.true) (list_length ix) ni hlen (nat_eqb_refl (list_length ix))) hfree)
 (fun (q : Nat) (ih : forall (i0 : Nat), forall (ix : ListType KExpr), @Eq Nat (list_length ix) ni -> @Eq Bool ((nig_indices_free_b block ix)) Bool.true -> @Eq Bool ((nig_args_b block d q i0 ni (list_append (nig_slots d q i0) ix))) Bool.true)
  (i0 : Nat) (ix : ListType KExpr) (hlen : @Eq Nat (list_length ix) ni) (hfree : @Eq Bool ((nig_indices_free_b block ix)) Bool.true) =>
  nig_and_intro (is_bvar_eq (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i0) (KExpr.bvar (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i0)))
   (nig_args_b block d q (Nat.succ i0) ni (list_append (nig_slots d q (Nat.succ i0)) ix))
   (nat_eqb_refl (Nat.sub (Nat.sub d (Nat.succ Nat.zero)) i0)) (ih (Nat.succ i0) ix hlen hfree)) p i",
    ),
    DeclarationInput::Proof(
        "nig_head_sound",
        r"forall (family : Name) (levels : ListType Level) (e : KExpr), @Eq Bool (nig_head_b family levels e) Bool.true -> @Eq KExpr e (KExpr.const family levels)",
        r"fun (family : Name) (levels : ListType Level) (e : KExpr) => @KExpr.rec (fun (e0 : KExpr) => @Eq Bool (nig_head_b family levels e0) Bool.true -> @Eq KExpr e0 (KExpr.const family levels))
 (fun (u : Level) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.sort u) (KExpr.const family levels)) h)
 (fun (j : Nat) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.bvar j) (KExpr.const family levels)) h)
 (fun (f : KExpr) (a : KExpr) (ih_f : @Eq Bool (nig_head_b family levels f) Bool.true -> @Eq KExpr f (KExpr.const family levels)) (ih_a : @Eq Bool (nig_head_b family levels a) Bool.true -> @Eq KExpr a (KExpr.const family levels)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.app f a) (KExpr.const family levels)) h)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_head_b family levels A) Bool.true -> @Eq KExpr A (KExpr.const family levels)) (ih_b : @Eq Bool (nig_head_b family levels b) Bool.true -> @Eq KExpr b (KExpr.const family levels)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.lam A b) (KExpr.const family levels)) h)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_head_b family levels A) Bool.true -> @Eq KExpr A (KExpr.const family levels)) (ih_b : @Eq Bool (nig_head_b family levels b) Bool.true -> @Eq KExpr b (KExpr.const family levels)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.pi A b) (KExpr.const family levels)) h)
 (fun (nm : Name) (us : ListType Level) => fun (h : @Eq Bool (Bool.and (name_eqb nm family) (ulist_eqb us levels)) Bool.true) =>
 universe_bridge_congr2 Name (ListType Level) KExpr KExpr.const nm family us levels
  (name_eqb_eq nm family (band_eq_true_left (name_eqb nm family) (ulist_eqb us levels) h))
  (ulist_eqb_eq us levels (band_eq_true_right (name_eqb nm family) (ulist_eqb us levels) h)))
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_head_b family levels A) Bool.true -> @Eq KExpr A (KExpr.const family levels)) (ih_v : @Eq Bool (nig_head_b family levels v) Bool.true -> @Eq KExpr v (KExpr.const family levels)) (ih_b : @Eq Bool (nig_head_b family levels b) Bool.true -> @Eq KExpr b (KExpr.const family levels)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.let_ A v b) (KExpr.const family levels)) h)
 (fun (S : Name) (j : Nat) (subject : KExpr) (ih_subject : @Eq Bool (nig_head_b family levels subject) Bool.true -> @Eq KExpr subject (KExpr.const family levels)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.proj S j subject) (KExpr.const family levels)) h)
 (fun (j : Nat) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq KExpr (KExpr.lit j) (KExpr.const family levels)) h) e",
    ),
    DeclarationInput::Proof(
        "nig_head_complete",
        r"forall (family : Name) (levels : ListType Level) (e : KExpr), @Eq KExpr e (KExpr.const family levels) -> @Eq Bool (nig_head_b family levels e) Bool.true",
        r"fun (family : Name) (levels : ListType Level) (e : KExpr) (h : @Eq KExpr e (KExpr.const family levels)) =>
 Eq.subst KExpr (fun (x : KExpr) => @Eq Bool (nig_head_b family levels x) Bool.true)
  (KExpr.const family levels) e (Eq.symm KExpr e (KExpr.const family levels) h)
  (nig_and_intro (name_eqb family family) (ulist_eqb levels levels) (name_eqb_refl family) (ulist_eqb_refl levels))",
    ),
    DeclarationInput::Inductive(
        r"inductive NamedStrictAppFacts (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) : Type
| mk : forall (ix : ListType KExpr) (head : @Eq KExpr (kapp_fn e) (KExpr.const family levels))
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true), NamedStrictAppFacts block levels family d p ni e",
    ),
    DeclarationInput::Proof(
        "nig_strict_sound",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), @Eq Bool (nig_strict_app_b block levels family d p ni e) Bool.true -> NamedStrictAppFacts block levels family d p ni e",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) (run : @Eq Bool (nig_strict_app_b block levels family d p ni e) Bool.true) =>
 nig_args_sound block d p Nat.zero ni (kapp_args e) (NamedStrictAppFacts block levels family d p ni e) (band_eq_true_right (nig_head_b family levels (kapp_fn e)) (nig_args_b block d p Nat.zero ni (kapp_args e)) run)
  (fun (ix : ListType KExpr)
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true) =>
   @NamedStrictAppFacts.mk block levels family d p ni e ix
    (nig_head_sound family levels (kapp_fn e) (band_eq_true_left (nig_head_b family levels (kapp_fn e)) (nig_args_b block d p Nat.zero ni (kapp_args e)) run)) spine length free)",
    ),
    DeclarationInput::Proof(
        "nig_strict_complete",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), NamedStrictAppFacts block levels family d p ni e -> @Eq Bool (nig_strict_app_b block levels family d p ni e) Bool.true",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) (facts : NamedStrictAppFacts block levels family d p ni e) => @NamedStrictAppFacts.rec block levels family d p ni e
 (fun (_facts : NamedStrictAppFacts block levels family d p ni e) => @Eq Bool (nig_strict_app_b block levels family d p ni e) Bool.true)
 (fun (ix : ListType KExpr) (head : @Eq KExpr (kapp_fn e) (KExpr.const family levels))
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true) => nig_and_intro (nig_head_b family levels (kapp_fn e)) (nig_args_b block d p Nat.zero ni (kapp_args e))
  (nig_head_complete family levels (kapp_fn e) head)
  (Eq.subst (ListType KExpr) (fun (as0 : (ListType KExpr)) => @Eq Bool (nig_args_b block d p Nat.zero ni as0) Bool.true)
   (list_append (nig_slots d p Nat.zero) ix) (kapp_args e)
   (Eq.symm (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix) spine)
   (nig_args_complete block d p Nat.zero ni ix length free))) facts",
    ),
    DeclarationInput::Proof(
        "nig_strict_decompose",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), NamedStrictAppFacts block levels family d p ni e -> forall (C : Type), (forall (ix : ListType KExpr), @Eq KExpr e (apply_spine (list_append (nig_slots d p Nat.zero) ix) (KExpr.const family levels)) -> @Eq Nat (list_length ix) ni -> @Eq Bool (nig_indices_free_b block ix) Bool.true -> C) -> C",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) (facts : NamedStrictAppFacts block levels family d p ni e) (C : Type)
 (k : forall (ix : ListType KExpr), @Eq KExpr e (apply_spine (list_append (nig_slots d p Nat.zero) ix) (KExpr.const family levels)) -> @Eq Nat (list_length ix) ni -> @Eq Bool (nig_indices_free_b block ix) Bool.true -> C) =>
 @NamedStrictAppFacts.rec block levels family d p ni e (fun (_facts : NamedStrictAppFacts block levels family d p ni e) => C)
 (fun (ix : ListType KExpr) (head : @Eq KExpr (kapp_fn e) (KExpr.const family levels))
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true) => k ix
  (Eq.trans KExpr e (apply_spine (kapp_args e) (kapp_fn e)) (apply_spine (list_append (nig_slots d p Nat.zero) ix) (KExpr.const family levels))
   (Eq.symm KExpr (apply_spine (kapp_args e) (kapp_fn e)) e (kapp_spine_roundtrip e))
   (universe_bridge_congr2 (ListType KExpr) KExpr KExpr apply_spine
    (kapp_args e) (list_append (nig_slots d p Nat.zero) ix) (kapp_fn e) (KExpr.const family levels) spine head)) length free) facts",
    ),
    DeclarationInput::Proof(
        "nig_strict_arity",
        r"forall (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr), NamedStrictAppFacts block levels family d p ni e -> @Eq Nat (list_length (kapp_args e)) (Nat.add p ni)",
        r"fun (block : ListType Name) (levels : ListType Level) (family : Name) (d p ni : Nat) (e : KExpr) (facts : NamedStrictAppFacts block levels family d p ni e) => @NamedStrictAppFacts.rec block levels family d p ni e
 (fun (_facts : NamedStrictAppFacts block levels family d p ni e) => @Eq Nat (list_length (kapp_args e)) (Nat.add p ni))
 (fun (ix : ListType KExpr) (head : @Eq KExpr (kapp_fn e) (KExpr.const family levels))
 (spine : @Eq (ListType KExpr) (kapp_args e) (list_append (nig_slots d p Nat.zero) ix))
 (length : @Eq Nat (list_length ix) ni) (free : @Eq Bool (nig_indices_free_b block ix) Bool.true) => Eq.trans Nat (list_length (kapp_args e))
  (list_length (list_append (nig_slots d p Nat.zero) ix)) (Nat.add p ni)
  (Eq.cong (ListType KExpr) Nat list_length (kapp_args e) (list_append (nig_slots d p Nat.zero) ix) spine)
  (Eq.trans Nat (list_length (list_append (nig_slots d p Nat.zero) ix))
   (Nat.add (list_length (nig_slots d p Nat.zero)) (list_length ix)) (Nat.add p ni)
   (list_append_length (nig_slots d p Nat.zero) ix)
   (universe_bridge_congr2 Nat Nat Nat Nat.add (list_length (nig_slots d p Nat.zero)) p (list_length ix) ni
    (nig_slots_length d p Nat.zero) length))) facts",
    ),
    DeclarationInput::Data(
        "nig_pi_prefix_b",
        r"forall (domains : ListType KExpr) (ct : KExpr), Bool",
        r"fun (domains : ListType KExpr) => @ListType.rec KExpr (fun (_ds : ListType KExpr) => KExpr -> Bool)
 (fun (_ct : KExpr) => Bool.true)
 (fun (domain : KExpr) (_ds : ListType KExpr) (ih : KExpr -> Bool) (ct : KExpr) => @KExpr.rec (fun (_e : KExpr) => Bool)
 (fun (u : Level) => Bool.false)
 (fun (j : Nat) => Bool.false)
 (fun (f : KExpr) (a : KExpr) (ih_f : Bool) (ih_a : Bool) => Bool.false)
 (fun (A : KExpr) (b : KExpr) (ih_A : Bool) (ih_b : Bool) => Bool.false)
 (fun (A : KExpr) (b : KExpr) (ih_A : Bool) (ih_b : Bool) => Bool.and (kexpr_beq domain A) (ih b))
 (fun (nm : Name) (us : ListType Level) => Bool.false)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : Bool) (ih_v : Bool) (ih_b : Bool) => Bool.false)
 (fun (S : Name) (j : Nat) (subject : KExpr) (ih_subject : Bool) => Bool.false)
 (fun (j : Nat) => Bool.false) ct) domains",
    ),
    DeclarationInput::Proof(
        "nig_prefix_bound",
        r"forall (domains : ListType KExpr) (ct : KExpr), @Eq Bool (nig_pi_prefix_b domains ct) Bool.true -> Le (list_length domains) (count_pi ct)",
        r"fun (domains : ListType KExpr) => @ListType.rec KExpr
 (fun (ds : ListType KExpr) => forall (ct : KExpr), @Eq Bool (nig_pi_prefix_b ds ct) Bool.true -> Le (list_length ds) (count_pi ct))
 (fun (ct : KExpr) (_h : @Eq Bool Bool.true Bool.true) => le_zero_n (count_pi ct))
 (fun (domain : KExpr) (ds : ListType KExpr)
  (ih : forall (ct : KExpr), @Eq Bool (nig_pi_prefix_b ds ct) Bool.true -> Le (list_length ds) (count_pi ct))
  (ct : KExpr) => @KExpr.rec (fun (e0 : KExpr) => @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) e0) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi e0))
 (fun (u : Level) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.sort u))) h)
 (fun (j : Nat) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.bvar j))) h)
 (fun (f : KExpr) (a : KExpr) (ih_f : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) f) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi f)) (ih_a : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) a) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi a)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.app f a))) h)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) A) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi A)) (ih_b : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) b) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi b)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.lam A b))) h)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) A) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi A)) (ih_b : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) b) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi b)) => fun (h : @Eq Bool (Bool.and (kexpr_beq domain A) (nig_pi_prefix_b ds b)) Bool.true) =>
 le_succ_succ (list_length ds) (count_pi b) (ih b (band_eq_true_right (kexpr_beq domain A) (nig_pi_prefix_b ds b) h)))
 (fun (nm : Name) (us : ListType Level) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.const nm us))) h)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) A) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi A)) (ih_v : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) v) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi v)) (ih_b : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) b) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi b)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.let_ A v b))) h)
 (fun (S : Name) (j : Nat) (subject : KExpr) (ih_subject : @Eq Bool (nig_pi_prefix_b (@ListType.cons KExpr domain ds) subject) Bool.true -> Le (Nat.succ (list_length ds)) (count_pi subject)) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.proj S j subject))) h)
 (fun (j : Nat) => fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (list_length ds)) (count_pi (KExpr.lit j))) h) ct) domains",
    ),
    DeclarationInput::Data(
        "nig_checked_indices",
        r"forall (p : Nat) (former : KExpr), OptionType Nat",
        r"fun (p : Nat) (former : KExpr) =>
 opt_pick Nat (nat_leb p (count_pi former)) (Nat.sub (count_pi former) p) (@OptionType.none Nat)",
    ),
    DeclarationInput::Proof(
        "nig_checked_indices_sound",
        r"forall (p ni : Nat) (former : KExpr), @Eq (OptionType Nat) (nig_checked_indices p former) (@OptionType.some Nat ni) -> @Eq Nat (count_pi former) (Nat.add p ni)",
        r"fun (p ni : Nat) (former : KExpr)
 (run : @Eq (OptionType Nat) (nig_checked_indices p former) (@OptionType.some Nat ni)) =>
 opt_pick_some_inv Nat (nat_leb p (count_pi former)) (Nat.sub (count_pi former) p) (@OptionType.none Nat) ni
  (@Eq Nat (count_pi former) (Nat.add p ni)) run
  (fun (bound : @Eq Bool (nat_leb p (count_pi former)) Bool.true) (chosen : @Eq Nat (Nat.sub (count_pi former) p) ni) =>
   Eq.trans Nat (count_pi former) (Nat.add (Nat.sub (count_pi former) p) p) (Nat.add p ni)
    (Eq.symm Nat (Nat.add (Nat.sub (count_pi former) p) p) (count_pi former)
     (nat_sub_add_cancel p (count_pi former) (ugeq_nat_leb_sound p (count_pi former) bound)))
    (Eq.trans Nat (Nat.add (Nat.sub (count_pi former) p) p) (Nat.add p (Nat.sub (count_pi former) p)) (Nat.add p ni)
     (nat_add_comm (Nat.sub (count_pi former) p) p)
     (Eq.cong Nat Nat (fun (n : Nat) => Nat.add p n) (Nat.sub (count_pi former) p) ni chosen)))
  (fun (_bound : @Eq Bool (nat_leb p (count_pi former)) Bool.false)
   (bad : @Eq (OptionType Nat) (@OptionType.none Nat) (@OptionType.some Nat ni)) =>
    option_none_ne_some Nat ni (@Eq Nat (count_pi former) (Nat.add p ni)) bad)",
    ),
    DeclarationInput::Data(
        "nig_member_indices",
        r"forall (p : Nat) (formers : ListType KExpr) (member : Nat), OptionType Nat",
        r"fun (p : Nat) (formers : ListType KExpr) (member : Nat) =>
 @OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType Nat) (@OptionType.none Nat)
  (fun (former : KExpr) => nig_checked_indices p former) (list_head (list_drop member formers))",
    ),
    DeclarationInput::Proof(
        "nig_selected_member_count",
        r"forall (p ni member : Nat) (formers : ListType KExpr) (former : KExpr), @Eq (OptionType KExpr) (list_head (list_drop member formers)) (@OptionType.some KExpr former) -> @Eq (OptionType Nat) (nig_member_indices p formers member) (@OptionType.some Nat ni) -> @Eq Nat (count_pi former) (Nat.add p ni)",
        r"fun (p ni member : Nat) (formers : ListType KExpr) (former : KExpr)
 (selected : @Eq (OptionType KExpr) (list_head (list_drop member formers)) (@OptionType.some KExpr former))
 (run : @Eq (OptionType Nat) (nig_member_indices p formers member) (@OptionType.some Nat ni)) =>
 nig_checked_indices_sound p ni former
  (Eq.subst (OptionType KExpr)
   (fun (o : OptionType KExpr) => @Eq (OptionType Nat)
    (@OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType Nat) (@OptionType.none Nat)
     (fun (ty : KExpr) => nig_checked_indices p ty) o) (@OptionType.some Nat ni))
   (list_head (list_drop member formers)) (@OptionType.some KExpr former) selected run)",
    ),
    DeclarationInput::Proof(
        "nig_or_elim_prop",
        r"forall (a b : Bool) (C : Prop), @Eq Bool (Bool.or a b) Bool.true -> (@Eq Bool a Bool.true -> C) -> (@Eq Bool b Bool.true -> C) -> C",
        r"fun (a b : Bool) (C : Prop) => @Bool.rec
 (fun (v : Bool) => @Eq Bool (Bool.or v b) Bool.true -> (@Eq Bool v Bool.true -> C) -> (@Eq Bool b Bool.true -> C) -> C)
 (fun (run : @Eq Bool b Bool.true) (_left : @Eq Bool Bool.false Bool.true -> C) (right : @Eq Bool b Bool.true -> C) => right run)
 (fun (_run : @Eq Bool Bool.true Bool.true) (left : @Eq Bool Bool.true Bool.true -> C) (_right : @Eq Bool b Bool.true -> C) => left (@Eq.refl Bool Bool.true)) a",
    ),
    DeclarationInput::Proof(
        "nig_block_free_sound",
        r"forall (block : ListType Name) (e : KExpr) (n : Name), @Eq Bool (nig_block_free_b block e) Bool.true -> @Eq Bool (name_list_mem block n) Bool.true -> @Eq Bool (const_occurs n e) Bool.false",
        r"fun (block : ListType Name) (e : KExpr) (n : Name) =>
 @ListType.rec Name
  (fun (ns : ListType Name) => @Eq Bool (nig_block_free_b ns e) Bool.true -> @Eq Bool (name_list_mem ns n) Bool.true -> @Eq Bool (const_occurs n e) Bool.false)
  (fun (_free : @Eq Bool Bool.true Bool.true) (member : @Eq Bool Bool.false Bool.true) =>
   bool_false_ne_true (@Eq Bool (const_occurs n e) Bool.false) member)
  (fun (a : Name) (ns : ListType Name)
   (ih : @Eq Bool (nig_block_free_b ns e) Bool.true -> @Eq Bool (name_list_mem ns n) Bool.true -> @Eq Bool (const_occurs n e) Bool.false)
   (free : @Eq Bool (Bool.and (Bool.not (const_occurs a e)) (nig_block_free_b ns e)) Bool.true)
   (member : @Eq Bool (Bool.or (name_eqb a n) (name_list_mem ns n)) Bool.true) =>
   nig_or_elim_prop (name_eqb a n) (name_list_mem ns n) (@Eq Bool (const_occurs n e) Bool.false) member
    (fun (same : @Eq Bool (name_eqb a n) Bool.true) =>
     Eq.subst Name (fun (nm : Name) => @Eq Bool (const_occurs nm e) Bool.false) a n (name_eqb_eq a n same)
      (nig_not_true_false (const_occurs a e)
       (band_eq_true_left (Bool.not (const_occurs a e)) (nig_block_free_b ns e) free)))
    (fun (tail : @Eq Bool (name_list_mem ns n) Bool.true) =>
     ih (band_eq_true_right (Bool.not (const_occurs a e)) (nig_block_free_b ns e) free) tail)) block",
    ),
    DeclarationInput::Proof(
        "nig_indices_free_at",
        r"forall (block : ListType Name) (j : Nat) (xs : ListType KExpr) (e : KExpr), @Eq Bool (nig_indices_free_b block xs) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop j xs)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true",
        r"fun (block : ListType Name) (j : Nat) (xs : ListType KExpr) (e : KExpr) => @Nat.rec
 (fun (j0 : Nat) => forall (ys : ListType KExpr), @Eq Bool (nig_indices_free_b block ys) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop j0 ys)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
 (fun (ys : ListType KExpr) => @ListType.rec KExpr (fun (zs : ListType KExpr) => @Eq Bool (nig_indices_free_b block zs) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop Nat.zero zs)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
  (fun (_free : @Eq Bool Bool.true Bool.true) (found : @Eq (OptionType KExpr) (list_head (list_drop Nat.zero (@ListType.nil KExpr))) (@OptionType.some KExpr e)) =>
 option_none_ne_some KExpr e (@Eq Bool (nig_block_free_b block e) Bool.true)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (list_head (list_drop Nat.zero (@ListType.nil KExpr))) (@OptionType.some KExpr e)
   (Eq.symm (OptionType KExpr) (list_head (list_drop Nat.zero (@ListType.nil KExpr))) (@OptionType.none KExpr)
    (Eq.cong (ListType KExpr) (OptionType KExpr) list_head (list_drop Nat.zero (@ListType.nil KExpr)) (@ListType.nil KExpr) (list_drop_nil Nat.zero))) found))
  (fun (a : KExpr) (tail : ListType KExpr) (_ih : @Eq Bool (nig_indices_free_b block tail) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop Nat.zero tail)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
   (free : @Eq Bool (Bool.and (nig_block_free_b block a) (nig_indices_free_b block tail)) Bool.true)
   (found : @Eq (OptionType KExpr) (@OptionType.some KExpr a) (@OptionType.some KExpr e)) =>
   Eq.subst KExpr (fun (x : KExpr) => @Eq Bool (nig_block_free_b block x) Bool.true) a e (option_some_inj KExpr a e found)
    (band_eq_true_left (nig_block_free_b block a) (nig_indices_free_b block tail) free)) ys)
 (fun (j0 : Nat) (ih : forall (ys : ListType KExpr), @Eq Bool (nig_indices_free_b block ys) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop j0 ys)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
  (ys : ListType KExpr) => @ListType.rec KExpr (fun (zs : ListType KExpr) => @Eq Bool (nig_indices_free_b block zs) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.succ j0) zs)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
   (fun (_free : @Eq Bool Bool.true Bool.true) (found : @Eq (OptionType KExpr) (list_head (list_drop (Nat.succ j0) (@ListType.nil KExpr))) (@OptionType.some KExpr e)) =>
 option_none_ne_some KExpr e (@Eq Bool (nig_block_free_b block e) Bool.true)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (list_head (list_drop (Nat.succ j0) (@ListType.nil KExpr))) (@OptionType.some KExpr e)
   (Eq.symm (OptionType KExpr) (list_head (list_drop (Nat.succ j0) (@ListType.nil KExpr))) (@OptionType.none KExpr)
    (Eq.cong (ListType KExpr) (OptionType KExpr) list_head (list_drop (Nat.succ j0) (@ListType.nil KExpr)) (@ListType.nil KExpr) (list_drop_nil (Nat.succ j0)))) found))
   (fun (a : KExpr) (tail : ListType KExpr) (_unused : @Eq Bool (nig_indices_free_b block tail) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.succ j0) tail)) (@OptionType.some KExpr e) -> @Eq Bool (nig_block_free_b block e) Bool.true)
    (free : @Eq Bool (Bool.and (nig_block_free_b block a) (nig_indices_free_b block tail)) Bool.true)
    (found : @Eq (OptionType KExpr) (list_head (list_drop (Nat.succ j0) (@ListType.cons KExpr a tail))) (@OptionType.some KExpr e)) =>
     ih tail (band_eq_true_right (nig_block_free_b block a) (nig_indices_free_b block tail) free) found) ys) j xs",
    ),
    DeclarationInput::Proof(
        "nig_index_excludes_member",
        r"forall (block : ListType Name) (ix : ListType KExpr) (j : Nat) (e : KExpr) (n : Name), @Eq Bool (nig_indices_free_b block ix) Bool.true -> @Eq (OptionType KExpr) (list_head (list_drop j ix)) (@OptionType.some KExpr e) -> @Eq Bool (name_list_mem block n) Bool.true -> @Eq Bool (const_occurs n e) Bool.false",
        r"fun (block : ListType Name) (ix : ListType KExpr) (j : Nat) (e : KExpr) (n : Name)
 (free : @Eq Bool (nig_indices_free_b block ix) Bool.true)
 (found : @Eq (OptionType KExpr) (list_head (list_drop j ix)) (@OptionType.some KExpr e))
 (member : @Eq Bool (name_list_mem block n) Bool.true) =>
 nig_block_free_sound block e n (nig_indices_free_at block j ix e free found) member",
    ),
    DeclarationInput::Data(
        "nig_param_levels",
        r"forall (params : ListType Name), ListType Level",
        r"fun (params : ListType Name) => @ListType.rec Name (fun (_ns : ListType Name) => ListType Level)
 (@ListType.nil Level) (fun (n : Name) (_ns : ListType Name) (ih : ListType Level) => @ListType.cons Level (Level.param n) ih) params",
    ),
    DeclarationInput::Data(
        "nig_pi_domains",
        r"forall (e : KExpr), ListType KExpr",
        r"fun (e : KExpr) => @KExpr.rec (fun (_e : KExpr) => ListType KExpr)
 (fun (u : Level) => @ListType.nil KExpr)
 (fun (i : Nat) => @ListType.nil KExpr)
 (fun (f : KExpr) (a : KExpr) (ih_f : ListType KExpr) (ih_a : ListType KExpr) => @ListType.nil KExpr)
 (fun (A : KExpr) (b : KExpr) (ih_A : ListType KExpr) (ih_b : ListType KExpr) => @ListType.nil KExpr)
 (fun (A : KExpr) (b : KExpr) (ih_A : ListType KExpr) (ih_b : ListType KExpr) => @ListType.cons KExpr A ih_b)
 (fun (n : Name) (us : ListType Level) => @ListType.nil KExpr)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : ListType KExpr) (ih_v : ListType KExpr) (ih_b : ListType KExpr) => @ListType.nil KExpr)
 (fun (S : Name) (i : Nat) (s : KExpr) (ih_s : ListType KExpr) => @ListType.nil KExpr)
 (fun (i : Nat) => @ListType.nil KExpr) e",
    ),
    DeclarationInput::Proof(
        "nig_pi_domains_length",
        r"forall (e : KExpr), @Eq Nat (list_length (nig_pi_domains e)) (count_pi e)",
        r"fun (e : KExpr) => @KExpr.rec (fun (e0 : KExpr) => @Eq Nat (list_length (nig_pi_domains e0)) (count_pi e0))
 (fun (u : Level) => @Eq.refl Nat Nat.zero)
 (fun (i : Nat) => @Eq.refl Nat Nat.zero)
 (fun (f : KExpr) (a : KExpr) (ih_f : @Eq Nat (list_length (nig_pi_domains f)) (count_pi f)) (ih_a : @Eq Nat (list_length (nig_pi_domains a)) (count_pi a)) => @Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Nat (list_length (nig_pi_domains A)) (count_pi A)) (ih_b : @Eq Nat (list_length (nig_pi_domains b)) (count_pi b)) => @Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (b : KExpr) (ih_A : @Eq Nat (list_length (nig_pi_domains A)) (count_pi A)) (ih_b : @Eq Nat (list_length (nig_pi_domains b)) (count_pi b)) => Eq.cong Nat Nat Nat.succ (list_length (nig_pi_domains b)) (count_pi b) ih_b)
 (fun (n : Name) (us : ListType Level) => @Eq.refl Nat Nat.zero)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ih_A : @Eq Nat (list_length (nig_pi_domains A)) (count_pi A)) (ih_v : @Eq Nat (list_length (nig_pi_domains v)) (count_pi v)) (ih_b : @Eq Nat (list_length (nig_pi_domains b)) (count_pi b)) => @Eq.refl Nat Nat.zero)
 (fun (S : Name) (i : Nat) (s : KExpr) (ih_s : @Eq Nat (list_length (nig_pi_domains s)) (count_pi s)) => @Eq.refl Nat Nat.zero)
 (fun (i : Nat) => @Eq.refl Nat Nat.zero) e",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nig_and_intro",
    "nig_not_true_false",
    "nig_slots_length",
    "nig_args_sound",
    "nig_args_complete",
    "nig_head_sound",
    "nig_head_complete",
    "nig_strict_sound",
    "nig_strict_complete",
    "nig_strict_decompose",
    "nig_strict_arity",
    "nig_prefix_bound",
    "nig_checked_indices_sound",
    "nig_selected_member_count",
    "nig_or_elim_prop",
    "nig_block_free_sound",
    "nig_indices_free_at",
    "nig_index_excludes_member",
    "nig_pi_domains_length",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "nig_block_free_b",
    "nig_indices_free_b",
    "nig_slots",
    "nig_args_b",
    "nig_head_b",
    "nig_strict_app_b",
    "nig_pi_prefix_b",
    "nig_checked_indices",
    "nig_member_indices",
    "nig_param_levels",
    "nig_pi_domains",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["NamedStrictAppFacts"];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nig_and_intro",
    "nig_not_true_false",
    "nig_slots_length",
    "nig_args_complete",
    "nig_head_sound",
    "nig_head_complete",
    "nig_strict_complete",
    "nig_strict_arity",
    "nig_prefix_bound",
    "nig_checked_indices_sound",
    "nig_selected_member_count",
    "nig_or_elim_prop",
    "nig_block_free_sound",
    "nig_indices_free_at",
    "nig_index_excludes_member",
    "nig_pi_domains_length",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] =
    &["nig_args_sound", "nig_strict_sound", "nig_strict_decompose"];
