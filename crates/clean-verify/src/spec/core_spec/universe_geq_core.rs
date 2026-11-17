// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-ordered, fuel-bounded raw universe comparison over mathematical Nat offsets.
//!
//! This is NOT source refinement of saturating u32 offsets, public normalize,
//! is_geq or max. Fuel exhaustion returns false. The companion stabilization
//! stage proves adequate fuel, not semantic completeness. Normalization
//! denotation and intermediate finite-offset bounds remain open.
//! Production source: level/mod.rs SHA256
//! efbb8a123f1a2eac24e6df3a95b20dbeb6a9dc03e4b90486f24b92be95c223b7.
//!
//! Pinned Lean 4.30.0-rc2 independently checked all 73 new declarations with
//! zero axioms against 74 exact exported dependency blocks from PJrAsR:
//! export SHA256 4a64c4995ca70fae3c7399eabeaa8e618eeba3cc0f7f65105856ec18086a9571.
//! Positive check: 0.29s, 431,570,944-byte max RSS, 1 GB reservation.
//! Exact checked slice SHA256:
//! c763e5e92fd0de5ddb67cd54ac0ff2ec8ba59e2d149cc4770dbfecb9e62b5ac1.
//! Reversed-order, RHS-OR and zero-fuel forged callers were rejected at their
//! intended type mismatches. The positive declarations also constructively
//! refute the reversed order and wrong RHS-OR order under concrete valuations.
//! See scratch/self-verification-universe-geq-core-2026-09-08.md.
//! Registered Clean checking and whole-corpus replay remain separate gates.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const ARITH: &[(&str, &str)] = &[
    (
        r"def ugeq_natMax_right (a : Nat) : forall (b : Nat), Le b (natMax a b) :=
 @Nat.rec (fun (x : Nat) => forall (b : Nat), Le b (natMax x b))
 (fun (b : Nat) => @Le.refl b)
 (fun (x : Nat) (ih : forall (b : Nat), Le b (natMax x b)) =>
  fun (b : Nat) => @Nat.rec (fun (y : Nat) => Le y (natMax (Nat.succ x) y))
   (le_zero_n (Nat.succ x))
   (fun (y : Nat) (_ : Le y (natMax (Nat.succ x) y)) => le_succ_succ y (natMax x y) (ih y)) b) a",
        "Right injection into the actual recursive natMax, proved by two Nat inductions.",
    ),
    (
        r"def ugeq_natMax_upper (a : Nat) : forall (b : Nat) (c : Nat), Le a c -> Le b c -> Le (natMax a b) c :=
 @Nat.rec (fun (x : Nat) => forall (b : Nat) (c : Nat), Le x c -> Le b c -> Le (natMax x b) c)
 (fun (b : Nat) (c : Nat) (_ : Le Nat.zero c) (hb : Le b c) => hb)
 (fun (x : Nat) (ih : forall (b : Nat) (c : Nat), Le x c -> Le b c -> Le (natMax x b) c) =>
  fun (b : Nat) => @Nat.rec
   (fun (y : Nat) => forall (c : Nat), Le (Nat.succ x) c -> Le y c -> Le (natMax (Nat.succ x) y) c)
   (fun (c : Nat) (hx : Le (Nat.succ x) c) (_ : Le Nat.zero c) => hx)
   (fun (y : Nat) (_ : forall (c : Nat), Le (Nat.succ x) c -> Le y c -> Le (natMax (Nat.succ x) y) c) =>
    fun (c : Nat) => @Nat.rec
     (fun (z : Nat) => Le (Nat.succ x) z -> Le (Nat.succ y) z -> Le (Nat.succ (natMax x y)) z)
     (fun (hx : Le (Nat.succ x) Nat.zero) (_ : Le (Nat.succ y) Nat.zero) =>
      nat_zero_ne_succ_beq x (Le (Nat.succ (natMax x y)) Nat.zero)
       (Eq.symm Nat (Nat.succ x) Nat.zero (le_zero_eq_zero (Nat.succ x) Nat.zero hx (@Eq.refl Nat Nat.zero))))
     (fun (z : Nat) (_ : Le (Nat.succ x) z -> Le (Nat.succ y) z -> Le (Nat.succ (natMax x y)) z) =>
      fun (hx : Le (Nat.succ x) (Nat.succ z)) (hy : Le (Nat.succ y) (Nat.succ z)) =>
       le_succ_succ (natMax x y) z (ih y z (le_succ_le_pred x (Nat.succ z) hx) (le_succ_le_pred y (Nat.succ z) hy))) c) b) a",
        "Maximum upper-bound introduction; both premises are necessary, with the impossible successor-below-zero arm refuted.",
    ),
    (
        r"def ugeq_natMax_comm (a : Nat) : forall (b : Nat), @Eq Nat (natMax a b) (natMax b a) :=
 @Nat.rec (fun (x : Nat) => forall (b : Nat), @Eq Nat (natMax x b) (natMax b x))
 (fun (b : Nat) => @Nat.rec (fun (y : Nat) => @Eq Nat y (natMax y Nat.zero))
  (@Eq.refl Nat Nat.zero) (fun (y : Nat) (_ : @Eq Nat y (natMax y Nat.zero)) => @Eq.refl Nat (Nat.succ y)) b)
 (fun (x : Nat) (ih : forall (b : Nat), @Eq Nat (natMax x b) (natMax b x)) =>
  fun (b : Nat) => @Nat.rec (fun (y : Nat) => @Eq Nat (natMax (Nat.succ x) y) (natMax y (Nat.succ x)))
   (@Eq.refl Nat (Nat.succ x))
   (fun (y : Nat) (_ : @Eq Nat (natMax (Nat.succ x) y) (natMax y (Nat.succ x))) =>
    Eq.cong Nat Nat Nat.succ (natMax x y) (natMax y x) (ih y)) b) a",
        "Commutativity of recursive natMax by structural induction, not source constructor equality.",
    ),
    (
        r"def ugeq_natMax_absorb_right (a : Nat) : forall (b : Nat), Le a b -> @Eq Nat (natMax a b) b :=
 @Nat.rec (fun (x : Nat) => forall (b : Nat), Le x b -> @Eq Nat (natMax x b) b)
 (fun (b : Nat) (_ : Le Nat.zero b) => @Eq.refl Nat b)
 (fun (x : Nat) (ih : forall (b : Nat), Le x b -> @Eq Nat (natMax x b) b) =>
  fun (b : Nat) => @Nat.rec (fun (y : Nat) => Le (Nat.succ x) y -> @Eq Nat (natMax (Nat.succ x) y) y)
   (fun (hx : Le (Nat.succ x) Nat.zero) =>
    nat_zero_ne_succ_beq x (@Eq Nat (Nat.succ x) Nat.zero)
     (Eq.symm Nat (Nat.succ x) Nat.zero (le_zero_eq_zero (Nat.succ x) Nat.zero hx (@Eq.refl Nat Nat.zero))))
   (fun (y : Nat) (_ : Le (Nat.succ x) y -> @Eq Nat (natMax (Nat.succ x) y) y) =>
    fun (hx : Le (Nat.succ x) (Nat.succ y)) =>
     Eq.cong Nat Nat Nat.succ (natMax x y) y (ih y (le_succ_le_pred x (Nat.succ y) hx))) b) a",
        "Semantic maximum absorption under a proved order; no comparator assumption.",
    ),
    (
        r"def ugeq_natMax_absorb_left (a : Nat) (b : Nat) (h : Le b a) : @Eq Nat (natMax a b) a :=
 Eq.trans Nat (natMax a b) (natMax b a) a (ugeq_natMax_comm a b) (ugeq_natMax_absorb_right b a h)",
        "Left absorption, derived from commutativity and right absorption.",
    ),
    (
        r"def ugeq_imax_upper (a : Nat) (b : Nat) : Le (imaxNat a b) (natMax a b) :=
 @Nat.rec (fun (y : Nat) => Le (imaxNat a y) (natMax a y))
 (le_zero_n (natMax a Nat.zero))
 (fun (y : Nat) (_ : Le (imaxNat a y) (natMax a y)) => @Le.refl (natMax a (Nat.succ y))) b",
        "imax is bounded above by max; this is one-way and remains valid at the zero pivot.",
    ),
    (
        r"def ugeq_imax_right (a : Nat) (b : Nat) : Le b (imaxNat a b) :=
 @Nat.rec (fun (y : Nat) => Le y (imaxNat a y)) (@Le.refl Nat.zero)
 (fun (y : Nat) (_ : Le y (imaxNat a y)) => ugeq_natMax_right a (Nat.succ y)) b",
        "The right operand is below imax, including the zero pivot; not the false converse advertised as iff in source comments.",
    ),
    (
        r"def ugeq_sub_zero_le (a : Nat) : forall (b : Nat), @Eq Nat (Nat.sub a b) Nat.zero -> Le a b :=
 @Nat.rec (fun (x : Nat) => forall (b : Nat), @Eq Nat (Nat.sub x b) Nat.zero -> Le x b)
 (fun (b : Nat) (_ : @Eq Nat (Nat.sub Nat.zero b) Nat.zero) => le_zero_n b)
 (fun (x : Nat) (ih : forall (b : Nat), @Eq Nat (Nat.sub x b) Nat.zero -> Le x b) =>
  fun (b : Nat) => @Nat.rec (fun (y : Nat) => @Eq Nat (Nat.sub (Nat.succ x) y) Nat.zero -> Le (Nat.succ x) y)
   (fun (h : @Eq Nat (Nat.sub (Nat.succ x) Nat.zero) Nat.zero) =>
    nat_zero_ne_succ_beq x (Le (Nat.succ x) Nat.zero)
     (Eq.symm Nat (Nat.succ x) Nat.zero (Eq.trans Nat (Nat.succ x) (Nat.sub (Nat.succ x) Nat.zero) Nat.zero
      (Eq.symm Nat (Nat.sub (Nat.succ x) Nat.zero) (Nat.succ x) (nat_sub_zero_right (Nat.succ x))) h)))
   (fun (y : Nat) (_ : @Eq Nat (Nat.sub (Nat.succ x) y) Nat.zero -> Le (Nat.succ x) y) =>
    fun (h : @Eq Nat (Nat.sub (Nat.succ x) (Nat.succ y)) Nat.zero) =>
     le_succ_succ x y (ih y (Eq.trans Nat (Nat.sub x y) (Nat.sub (Nat.succ x) (Nat.succ y)) Nat.zero
      (Eq.symm Nat (Nat.sub (Nat.succ x) (Nat.succ y)) (Nat.sub x y) (nat_sub_succ_succ x y)) h))) b) a",
        "Reflects zero truncated subtraction into actual Le by two Nat inductions.",
    ),
    (
        r"def ugeq_nat_leb_sound (a : Nat) (b : Nat) (h : @Eq Bool (nat_leb a b) Bool.true) : Le a b :=
 ugeq_sub_zero_le a b (nat_is_zero_eq (Nat.sub a b) h)",
        "Reflects the actual nat_leb arithmetic guard; no guard-correctness hypothesis.",
    ),
    (
        r"def ugeq_add_left_mono (a : Nat) (b : Nat) (c : Nat) (h : Le a b) : Le (Nat.add c a) (Nat.add c b) :=
 Eq.substType Nat (fun (z : Nat) => Le z (Nat.add c b)) (Nat.add a c) (Nat.add c a) (nat_add_comm a c)
  (Eq.substType Nat (fun (z : Nat) => Le (Nat.add a c) z) (Nat.add b c) (Nat.add c b) (nat_add_comm b c)
   (le_add_right_mono a b c h))",
        "Left-addition monotonicity, reusing the existing right-addition theorem.",
    ),
    (
        r"def ugeq_level_zero (a : Level) (h : @Eq Bool (level_is_zero a) Bool.true) (rho : Name -> Nat) :
 @Eq Nat (evalL rho a) Nat.zero :=
 Eq.trans Nat (evalL rho a) (level_eval rho a) Nat.zero
 (Eq.symm Nat (level_eval rho a) (evalL rho a) (level_eval_eq_evalL rho a)) (level_is_zero_sound a h rho)",
        "Transports the existing definitely-zero proof to the actual semantic evalL.",
    ),
    (
        r"def ugeq_or_cases (a : Bool) (b : Bool) (h : @Eq Bool (Bool.or a b) Bool.true) (C : Prop)
 (ha : @Eq Bool a Bool.true -> C) (hb : @Eq Bool b Bool.true -> C) : C :=
 @Bool.rec (fun (q : Bool) => @Eq Bool a q -> C)
 (fun (eq : @Eq Bool a Bool.false) => hb (bor_false_case b a eq h))
 (fun (eq : @Eq Bool a Bool.true) => ha eq) a (@Eq.refl Bool a)",
        "Actual Bool.or inversion used only for sufficient disjunction branches.",
    ),
];

const OFFSET: &[(&str, &str)] = &[
    (
        r"def level_offset_base (a : Level) : Level :=
 @Level.rec (fun (_ : Level) => Level) Level.zero
 (fun (_ : Level) (base : Level) => base)
 (fun (x : Level) (y : Level) (_ : Level) (_ : Level) => Level.max x y)
 (fun (x : Level) (y : Level) (_ : Level) (_ : Level) => Level.imax x y)
 (fun (n : Name) => Level.param n) a",
        "Strips all outer successor constructors; raw mathematical model, not u32 offset refinement.",
    ),
    (
        r"def level_offset_nat (a : Level) : Nat :=
 @Level.rec (fun (_ : Level) => Nat) Nat.zero
 (fun (_ : Level) (count : Nat) => Nat.succ count)
 (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => Nat.zero)
 (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => Nat.zero)
 (fun (_ : Name) => Nat.zero) a",
        "Exact natural successor count, deliberately not the source saturating u32 count.",
    ),
    (
        r"def level_strip_offset_eval (rho : Name -> Nat) (a : Level) :
 @Eq Nat (evalL rho a) (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a)) :=
 @Level.rec
 (fun (x : Level) => @Eq Nat (evalL rho x) (Nat.add (evalL rho (level_offset_base x)) (level_offset_nat x)))
 (@Eq.refl Nat Nat.zero)
 (fun (x : Level) (ih : @Eq Nat (evalL rho x) (Nat.add (evalL rho (level_offset_base x)) (level_offset_nat x))) =>
  Eq.cong Nat Nat (fun (n : Nat) => Nat.succ n) (evalL rho x)
   (Nat.add (evalL rho (level_offset_base x)) (level_offset_nat x)) ih)
 (fun (x : Level) (y : Level) (_ : @Eq Nat (evalL rho x) (Nat.add (evalL rho (level_offset_base x)) (level_offset_nat x)))
 (_ : @Eq Nat (evalL rho y) (Nat.add (evalL rho (level_offset_base y)) (level_offset_nat y))) =>
  @Eq.refl Nat (natMax (evalL rho x) (evalL rho y)))
 (fun (x : Level) (y : Level) (_ : @Eq Nat (evalL rho x) (Nat.add (evalL rho (level_offset_base x)) (level_offset_nat x)))
 (_ : @Eq Nat (evalL rho y) (Nat.add (evalL rho (level_offset_base y)) (level_offset_nat y))) =>
  @Eq.refl Nat (imaxNat (evalL rho x) (evalL rho y)))
 (fun (n : Name) => @Eq.refl Nat (rho n)) a",
        "All five raw level constructors satisfy base-plus-exact-Nat-offset denotation.",
    ),
    (
        r"def ugeq_equal_order (a : Level) (b : Level) (h : @Eq Level a b) : levelLeqSem b a :=
 Eq.substType Level (fun (x : Level) => levelLeqSem b x) b a (Eq.symm Level a b h) (levelLeqSem_refl b)",
        "Structural equality supplies semantic order in the comparator's greater-than direction.",
    ),
    (
        r"def ugeq_zero_order (a : Level) (b : Level) (h : @Eq Bool (level_is_zero b) Bool.true) : levelLeqSem b a :=
 fun (rho : Name -> Nat) => Eq.substType Nat (fun (n : Nat) => Le n (evalL rho a))
 Nat.zero (evalL rho b) (Eq.symm Nat (evalL rho b) Nat.zero (ugeq_level_zero b h rho)) (le_zero_n (evalL rho a))",
        "Definitely-zero RHS is below every level by the proved recursive zero classifier.",
    ),
    (
        r"def ugeq_offset_base_below (a : Level) : levelLeqSem (level_offset_base a) a :=
 fun (rho : Name -> Nat) => Eq.substType Nat (fun (n : Nat) => Le (evalL rho (level_offset_base a)) n)
 (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a)) (evalL rho a)
 (Eq.symm Nat (evalL rho a) (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a)) (level_strip_offset_eval rho a))
 (le_add_self_left (evalL rho (level_offset_base a)) (level_offset_nat a))",
        "The exact stripped base is below the original level for arbitrary raw trees.",
    ),
    (
        r"def ugeq_offset_mono (a : Level) (b : Level)
 (hb : levelLeqSem (level_offset_base b) (level_offset_base a))
 (ho : Le (level_offset_nat b) (level_offset_nat a)) : levelLeqSem b a :=
 fun (rho : Name -> Nat) =>
 Eq.substType Nat (fun (x : Nat) => Le x (evalL rho a))
 (Nat.add (evalL rho (level_offset_base b)) (level_offset_nat b)) (evalL rho b)
 (Eq.symm Nat (evalL rho b) (Nat.add (evalL rho (level_offset_base b)) (level_offset_nat b)) (level_strip_offset_eval rho b))
 (Eq.substType Nat
  (fun (x : Nat) => Le (Nat.add (evalL rho (level_offset_base b)) (level_offset_nat b)) x)
  (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a)) (evalL rho a)
  (Eq.symm Nat (evalL rho a) (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a)) (level_strip_offset_eval rho a))
  (le_trans (Nat.add (evalL rho (level_offset_base b)) (level_offset_nat b))
   (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat b))
   (Nat.add (evalL rho (level_offset_base a)) (level_offset_nat a))
   (le_add_right_mono (evalL rho (level_offset_base b)) (evalL rho (level_offset_base a)) (level_offset_nat b) (hb rho))
   (ugeq_add_left_mono (level_offset_nat b) (level_offset_nat a) (evalL rho (level_offset_base a)) ho)))",
        "Natural-offset comparison is sound when both actual base order and exact count order are derived.",
    ),
    (
        r"def ugeq_choose_cases (g : Bool) (x : Bool) (y : Bool) (C : Prop)
 (hx : @Eq Bool g Bool.false -> @Eq Bool x Bool.true -> C)
 (hy : @Eq Bool g Bool.true -> @Eq Bool y Bool.true -> C)
 (h : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y g) Bool.true) : C :=
 @Bool.rec
 (fun (q : Bool) => @Eq Bool g q -> @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y q) Bool.true -> C)
 hx hy g (@Eq.refl Bool g) h",
        "One exact Bool.rec branch split; it preserves both the selected guard equation and successful branch result.",
    ),
    (
        r"def ugeq_max_below (a : Level) (b : Level) (c : Level)
 (ha : levelLeqSem a c) (hb : levelLeqSem b c) : levelLeqSem (Level.max a b) c :=
 fun (rho : Name -> Nat) => ugeq_natMax_upper (evalL rho a) (evalL rho b) (evalL rho c) (ha rho) (hb rho)",
        "RHS Max requires both actual recursive suborders.",
    ),
    (
        r"def ugeq_below_max_left (a : Level) (b : Level) (c : Level)
 (h : levelLeqSem c a) : levelLeqSem c (Level.max a b) :=
 fun (rho : Name -> Nat) => le_trans (evalL rho c) (evalL rho a) (natMax (evalL rho a) (evalL rho b))
 (h rho) (le_natMax_left (evalL rho a) (evalL rho b))",
        "Either successful left-Max recursive branch is sufficient, first branch.",
    ),
    (
        r"def ugeq_below_max_right (a : Level) (b : Level) (c : Level)
 (h : levelLeqSem c b) : levelLeqSem c (Level.max a b) :=
 fun (rho : Name -> Nat) => le_trans (evalL rho c) (evalL rho b) (natMax (evalL rho a) (evalL rho b))
 (h rho) (ugeq_natMax_right (evalL rho a) (evalL rho b))",
        "Either successful left-Max recursive branch is sufficient, second branch.",
    ),
    (
        r"def ugeq_imax_below (a : Level) (b : Level) (c : Level)
 (ha : levelLeqSem a c) (hb : levelLeqSem b c) : levelLeqSem (Level.imax a b) c :=
 fun (rho : Name -> Nat) => le_trans (imaxNat (evalL rho a) (evalL rho b))
 (natMax (evalL rho a) (evalL rho b)) (evalL rho c)
 (ugeq_imax_upper (evalL rho a) (evalL rho b))
 (ugeq_natMax_upper (evalL rho a) (evalL rho b) (evalL rho c) (ha rho) (hb rho))",
        "RHS IMax conjunction is sufficient via imax <= max, without claiming an iff.",
    ),
    (
        r"def ugeq_below_imax_right (a : Level) (b : Level) (c : Level)
 (h : levelLeqSem c b) : levelLeqSem c (Level.imax a b) :=
 fun (rho : Name -> Nat) => le_trans (evalL rho c) (evalL rho b) (imaxNat (evalL rho a) (evalL rho b))
 (h rho) (ugeq_imax_right (evalL rho a) (evalL rho b))",
        "Left IMax may use a successful comparison against its right child; no converse or nonzero assumption.",
    ),
];

const MODEL: &[(&str, &str)] = &[
    (
        r"def level_offset_positive (a : Level) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false (nat_is_zero (level_offset_nat a))",
        "The raw exact-Nat offset >0 guard, not a bounded machine integer comparison.",
    ),
    (
        r"def level_geq_offsets (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) Bool.false
   (next (level_offset_base a) (level_offset_base b))
   (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)))
  (nat_leb (level_offset_nat b) (level_offset_nat a))
  (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b)))",
        "Exact source-ordered final raw-core offset guards over mathematical counts.",
    ),
    (
        r"def level_geq_imax_left (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_offsets next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_offsets next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_offsets next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => next y b)
 (fun (_ : Name) => level_geq_offsets next a b) a",
        "Left-IMax dispatch after RHS-IMax; otherwise the final offset comparison.",
    ),
    (
        r"def level_geq_imax_right (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_imax_left next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_imax_left next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_imax_left next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => Bool.and (next a x) (next a y))
 (fun (_ : Name) => level_geq_imax_left next a b) b",
        "RHS-IMax conjunction before left-IMax, including the zero-pivot cases.",
    ),
    (
        r"def level_geq_max_left (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_imax_right next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_imax_right next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => @Bool.rec (fun (_ : Bool) => Bool) (level_geq_imax_right next a b) Bool.true (Bool.or (next x b) (next y b)))
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_imax_right next a b)
 (fun (_ : Name) => level_geq_imax_right next a b) a",
        "Production left-Max success returns true; failure deliberately falls through to RHS-IMax, not false.",
    ),
    (
        r"def level_geq_max_right (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_max_left next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_max_left next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => Bool.and (next a x) (next a y))
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_max_left next a b)
 (fun (_ : Name) => level_geq_max_left next a b) b",
        "Production first structural branch is the RHS-Max conjunction.",
    ),
    (
        r"def level_geq_core_step (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right next a b) Bool.true
   (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)))
  Bool.true (Bool.or (level_eqb a b) (level_is_zero b))",
        "One source-ordered recursive raw-core layer, with equality/zero and positive-offset-base fast paths before structural guards; memo-table erased only at this model layer.",
    ),
    (
        r"def level_geq_core_fuel (fuel : Nat) (a : Level) (b : Level) : Bool :=
 @Nat.rec (fun (_ : Nat) => Level -> Level -> Bool)
 (fun (_ : Level) (_ : Level) => Bool.false)
 (fun (_ : Nat) (next : Level -> Level -> Bool) => level_geq_core_step next) fuel a b",
        "Finite recursive raw-core model. Every recursive call consumes one fuel; exhaustion rejects. No stabilization, completeness, source execution or normalization claim.",
    ),
];

const SOUND: &[(&str, &str)] = &[
    (
        r"def ugeq_offsets_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) (h : @Eq Bool (level_geq_offsets next a b) Bool.true) : levelLeqSem b a :=
 ugeq_choose_cases (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) (@Bool.rec (fun (_ : Bool) => Bool) Bool.false (next (level_offset_base a) (level_offset_base b)) (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a))) (nat_leb (level_offset_nat b) (level_offset_nat a)) (levelLeqSem b a)
 (fun (_ : @Eq Bool (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) Bool.false) (h2 : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) Bool.false (next (level_offset_base a) (level_offset_base b)) (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a))) Bool.true) =>
  ugeq_choose_cases (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.false (next (level_offset_base a) (level_offset_base b)) (levelLeqSem b a)
   (fun (_ : @Eq Bool (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.false) (bad : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (levelLeqSem b a) bad)
   (fun (hg : @Eq Bool (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.true) (hn : @Eq Bool (next (level_offset_base a) (level_offset_base b)) Bool.true) =>
    ugeq_offset_mono a b (hs (level_offset_base a) (level_offset_base b) hn)
     (Eq.substType Nat (fun (n : Nat) => Le n (level_offset_nat a))
      (level_offset_nat a) (level_offset_nat b)
      (nat_eqb_eq (level_offset_nat a) (level_offset_nat b)
       (band_eq_true_left (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a) hg))
      (@Le.refl (level_offset_nat a)))) h2)
 (fun (hg : @Eq Bool (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) Bool.true) (hc : @Eq Bool (nat_leb (level_offset_nat b) (level_offset_nat a)) Bool.true) =>
  ugeq_or_cases (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b)) hg (levelLeqSem b a)
   (fun (he : @Eq Bool (level_eqb (level_offset_base a) (level_offset_base b)) Bool.true) =>
    ugeq_offset_mono a b (ugeq_equal_order (level_offset_base a) (level_offset_base b)
     (level_eqb_eq (level_offset_base a) (level_offset_base b) he))
     (ugeq_nat_leb_sound (level_offset_nat b) (level_offset_nat a) hc))
   (fun (hz : @Eq Bool (level_is_zero (level_offset_base b)) Bool.true) =>
    ugeq_offset_mono a b (ugeq_zero_order (level_offset_base a) (level_offset_base b) hz)
     (ugeq_nat_leb_sound (level_offset_nat b) (level_offset_nat a) hc))) h",
        "Final source-ordered offset branches preserve semantic order, using derived arithmetic and only the smaller-fuel induction hypothesis.",
    ),
    (
        r"def ugeq_imax_left_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) : @Eq Bool (level_geq_imax_left next a b) Bool.true -> levelLeqSem b a :=
 @Level.rec (fun (z : Level) => @Eq Bool (level_geq_imax_left next z b) Bool.true -> levelLeqSem b z)
 (ugeq_offsets_sound next hs Level.zero b)
 (fun (x : Level) (_ : @Eq Bool (level_geq_imax_left next x b) Bool.true -> levelLeqSem b x) => ugeq_offsets_sound next hs (Level.succ x) b)
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_imax_left next x b) Bool.true -> levelLeqSem b x) (_ : @Eq Bool (level_geq_imax_left next y b) Bool.true -> levelLeqSem b y) => ugeq_offsets_sound next hs (Level.max x y) b)
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_imax_left next x b) Bool.true -> levelLeqSem b x) (_ : @Eq Bool (level_geq_imax_left next y b) Bool.true -> levelLeqSem b y) => fun (h : @Eq Bool (next y b) Bool.true) => ugeq_below_imax_right x y b (hs y b h))
 (fun (n : Name) => ugeq_offsets_sound next hs (Level.param n) b) a",
        "All five left-head cases; successful IMax recursion uses its proved right-child lower bound.",
    ),
    (
        r"def ugeq_imax_right_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) : @Eq Bool (level_geq_imax_right next a b) Bool.true -> levelLeqSem b a :=
 @Level.rec (fun (z : Level) => @Eq Bool (level_geq_imax_right next a z) Bool.true -> levelLeqSem z a)
 (ugeq_imax_left_sound next hs a Level.zero)
 (fun (x : Level) (_ : @Eq Bool (level_geq_imax_right next a x) Bool.true -> levelLeqSem x a) => ugeq_imax_left_sound next hs a (Level.succ x))
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_imax_right next a x) Bool.true -> levelLeqSem x a) (_ : @Eq Bool (level_geq_imax_right next a y) Bool.true -> levelLeqSem y a) => ugeq_imax_left_sound next hs a (Level.max x y))
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_imax_right next a x) Bool.true -> levelLeqSem x a) (_ : @Eq Bool (level_geq_imax_right next a y) Bool.true -> levelLeqSem y a) => fun (h : @Eq Bool (Bool.and (next a x) (next a y)) Bool.true) =>
 ugeq_imax_below x y a (hs a x (band_eq_true_left (next a x) (next a y) h))
  (hs a y (band_eq_true_right (next a x) (next a y) h)))
 (fun (n : Name) => ugeq_imax_left_sound next hs a (Level.param n)) b",
        "All five right-head cases; RHS IMax requires both smaller-fuel successes.",
    ),
    (
        r"def ugeq_max_left_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) : @Eq Bool (level_geq_max_left next a b) Bool.true -> levelLeqSem b a :=
 @Level.rec (fun (z : Level) => @Eq Bool (level_geq_max_left next z b) Bool.true -> levelLeqSem b z)
 (ugeq_imax_right_sound next hs Level.zero b)
 (fun (x : Level) (_ : @Eq Bool (level_geq_max_left next x b) Bool.true -> levelLeqSem b x) => ugeq_imax_right_sound next hs (Level.succ x) b)
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_max_left next x b) Bool.true -> levelLeqSem b x) (_ : @Eq Bool (level_geq_max_left next y b) Bool.true -> levelLeqSem b y) => fun (h : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_imax_right next (Level.max x y) b) Bool.true
  (Bool.or (next x b) (next y b))) Bool.true) =>
 ugeq_choose_cases (Bool.or (next x b) (next y b)) (level_geq_imax_right next (Level.max x y) b) Bool.true (levelLeqSem b (Level.max x y))
  (fun (_ : @Eq Bool (Bool.or (next x b) (next y b)) Bool.false) (hf : @Eq Bool (level_geq_imax_right next (Level.max x y) b) Bool.true) =>
   ugeq_imax_right_sound next hs (Level.max x y) b hf)
  (fun (hg : @Eq Bool (Bool.or (next x b) (next y b)) Bool.true) (_ : @Eq Bool Bool.true Bool.true) =>
   ugeq_or_cases (next x b) (next y b) hg (levelLeqSem b (Level.max x y))
    (fun (hx : @Eq Bool (next x b) Bool.true) => ugeq_below_max_left x y b (hs x b hx))
    (fun (hy : @Eq Bool (next y b) Bool.true) => ugeq_below_max_right x y b (hs y b hy))) h)
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_max_left next x b) Bool.true -> levelLeqSem b x) (_ : @Eq Bool (level_geq_max_left next y b) Bool.true -> levelLeqSem b y) => ugeq_imax_right_sound next hs (Level.imax x y) b)
 (fun (n : Name) => ugeq_imax_right_sound next hs (Level.param n) b) a",
        "Crucial production fallthrough is proved: failed left-Max disjunction continues through the right-IMax proof, never concludes non-order.",
    ),
    (
        r"def ugeq_max_right_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) : @Eq Bool (level_geq_max_right next a b) Bool.true -> levelLeqSem b a :=
 @Level.rec (fun (z : Level) => @Eq Bool (level_geq_max_right next a z) Bool.true -> levelLeqSem z a)
 (ugeq_max_left_sound next hs a Level.zero)
 (fun (x : Level) (_ : @Eq Bool (level_geq_max_right next a x) Bool.true -> levelLeqSem x a) => ugeq_max_left_sound next hs a (Level.succ x))
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_max_right next a x) Bool.true -> levelLeqSem x a) (_ : @Eq Bool (level_geq_max_right next a y) Bool.true -> levelLeqSem y a) => fun (h : @Eq Bool (Bool.and (next a x) (next a y)) Bool.true) =>
 ugeq_max_below x y a (hs a x (band_eq_true_left (next a x) (next a y) h))
  (hs a y (band_eq_true_right (next a x) (next a y) h)))
 (fun (x : Level) (y : Level) (_ : @Eq Bool (level_geq_max_right next a x) Bool.true -> levelLeqSem x a) (_ : @Eq Bool (level_geq_max_right next a y) Bool.true -> levelLeqSem y a) => ugeq_max_left_sound next hs a (Level.imax x y))
 (fun (n : Name) => ugeq_max_left_sound next hs a (Level.param n)) b",
        "RHS Max is handled before all other structural cases, with both recursive orders derived.",
    ),
    (
        r"def ugeq_core_step_sound (next : Level -> Level -> Bool) (hs : forall (x : Level) (y : Level), @Eq Bool (next x y) Bool.true -> levelLeqSem y x)
 (a : Level) (b : Level) (h : @Eq Bool (level_geq_core_step next a b) Bool.true) : levelLeqSem b a :=
 ugeq_choose_cases (Bool.or (level_eqb a b) (level_is_zero b)) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right next a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true (levelLeqSem b a)
 (fun (_ : @Eq Bool (Bool.or (level_eqb a b) (level_is_zero b)) Bool.false) (hr : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right next a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true) =>
  ugeq_choose_cases (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) (level_geq_max_right next a b) Bool.true (levelLeqSem b a)
   (fun (_ : @Eq Bool (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) Bool.false) (hf : @Eq Bool (level_geq_max_right next a b) Bool.true) =>
    ugeq_max_right_sound next hs a b hf)
   (fun (hg : @Eq Bool (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) Bool.true) (_ : @Eq Bool Bool.true Bool.true) =>
    Eq.substType Level (fun (z : Level) => levelLeqSem z a) (level_offset_base a) b
     (level_eqb_eq (level_offset_base a) b
      (band_eq_true_right (level_offset_positive a) (level_eqb (level_offset_base a) b) hg))
     (ugeq_offset_base_below a)) hr)
 (fun (hg : @Eq Bool (Bool.or (level_eqb a b) (level_is_zero b)) Bool.true) (_ : @Eq Bool Bool.true Bool.true) =>
  ugeq_or_cases (level_eqb a b) (level_is_zero b) hg (levelLeqSem b a)
   (fun (he : @Eq Bool (level_eqb a b) Bool.true) => ugeq_equal_order a b (level_eqb_eq a b he))
   (fun (hz : @Eq Bool (level_is_zero b) Bool.true) => ugeq_zero_order a b hz)) h",
        "One comparator layer is proved from the actual induction hypothesis; initial equality, recursive-zero and positive-base guards precede structural dispatch.",
    ),
    (
        r"def level_geq_core_fuel_sound (fuel : Nat) : forall (a : Level) (b : Level),
 @Eq Bool (level_geq_core_fuel fuel a b) Bool.true -> levelLeqSem b a :=
 @Nat.rec
 (fun (f : Nat) => forall (a : Level) (b : Level), @Eq Bool (level_geq_core_fuel f a b) Bool.true -> levelLeqSem b a)
 (fun (a : Level) (b : Level) (bad : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (levelLeqSem b a) bad)
 (fun (f : Nat) (ih : forall (a : Level) (b : Level), @Eq Bool (level_geq_core_fuel f a b) Bool.true -> levelLeqSem b a) =>
  fun (a : Level) (b : Level) (h : @Eq Bool (level_geq_core_fuel (Nat.succ f) a b) Bool.true) =>
   ugeq_core_step_sound (level_geq_core_fuel f) ih a b h) fuel",
        "Actual fuel induction proves every successful raw comparison semantically sound. No comparator-soundness premise remains; no result is claimed for false, fuel adequacy, public normalization or saturating offsets.",
    ),
];

const MAX_CALLER: &[(&str, &str)] = &[
    (
        r"def ugeq_choose_level (g : Bool) (x : Level) (y : Level) (P : Level -> Prop)
 (hx : @Eq Bool g Bool.false -> P x) (hy : @Eq Bool g Bool.true -> P y) :
 P (@Bool.rec (fun (_ : Bool) => Level) x y g) :=
 @Bool.rec (fun (q : Bool) => @Eq Bool g q -> P (@Bool.rec (fun (_ : Bool) => Level) x y q))
 hx hy g (@Eq.refl Bool g)",
        "Selects a concrete level-valued branch with the real guard equation retained.",
    ),
    (
        r"def ugeq_max_return_left (a : Level) (b : Level) (h : levelLeqSem b a) : levelEqSem a (Level.max a b) :=
 fun (rho : Name -> Nat) => Eq.symm Nat (natMax (evalL rho a) (evalL rho b)) (evalL rho a)
 (ugeq_natMax_absorb_left (evalL rho a) (evalL rho b) (h rho))",
        "Semantic correctness of returning the left operand once actual order is proved.",
    ),
    (
        r"def ugeq_max_return_right (a : Level) (b : Level) (h : levelLeqSem a b) : levelEqSem b (Level.max a b) :=
 fun (rho : Name -> Nat) => Eq.symm Nat (natMax (evalL rho a) (evalL rho b)) (evalL rho b)
 (ugeq_natMax_absorb_right (evalL rho a) (evalL rho b) (h rho))",
        "Semantic correctness of returning the right operand once actual order is proved.",
    ),
    (
        r"def level_max_core_subsume (fuel : Nat) (a : Level) (b : Level) : Level :=
 @Bool.rec (fun (_ : Bool) => Level)
 (@Bool.rec (fun (_ : Bool) => Level) (Level.max a b) b (level_geq_core_fuel fuel b a))
 a (level_geq_core_fuel fuel a b)",
        "Both raw/fuel subsumption arms, left first, then right, then a raw Max fallback. Not public normalized source max.",
    ),
    (
        r"def level_max_core_subsume_sound (fuel : Nat) (a : Level) (b : Level) :
 levelEqSem (level_max_core_subsume fuel a b) (Level.max a b) :=
 ugeq_choose_level (level_geq_core_fuel fuel a b)
 (@Bool.rec (fun (_ : Bool) => Level) (Level.max a b) b (level_geq_core_fuel fuel b a))
 a (fun (x : Level) => levelEqSem x (Level.max a b))
 (fun (_ : @Eq Bool (level_geq_core_fuel fuel a b) Bool.false) =>
  ugeq_choose_level (level_geq_core_fuel fuel b a) (Level.max a b) b
   (fun (x : Level) => levelEqSem x (Level.max a b))
   (fun (_ : @Eq Bool (level_geq_core_fuel fuel b a) Bool.false) => levelEqSem_refl (Level.max a b))
   (fun (h : @Eq Bool (level_geq_core_fuel fuel b a) Bool.true) =>
    ugeq_max_return_right a b (level_geq_core_fuel_sound fuel b a h)))
 (fun (h : @Eq Bool (level_geq_core_fuel fuel a b) Bool.true) =>
  ugeq_max_return_left a b (level_geq_core_fuel_sound fuel a b h))",
        "Actual caller of the fuel-induction theorem in each subsumption arm; fallback is semantic reflexivity, not a non-order claim.",
    ),
    (
        r"def level_max_core_fuel (fuel : Nat) (a : Level) (b : Level) : Level :=
 @Bool.rec (fun (_ : Bool) => Level) (@Bool.rec (fun (_ : Bool) => Level) (@Bool.rec (fun (_ : Bool) => Level) (level_max_core_subsume fuel a b) a (level_is_zero b)) b (level_is_zero a)) a (level_eqb a b)",
        "Source-ordered max guard structure with the deliberately raw/fuel comparator substituted for the source public normalized comparator. Distinct name preserves that scope boundary.",
    ),
    (
        r"def level_max_core_fuel_sound (fuel : Nat) (a : Level) (b : Level) :
 levelEqSem (level_max_core_fuel fuel a b) (Level.max a b) :=
 ugeq_choose_level (level_eqb a b) (@Bool.rec (fun (_ : Bool) => Level) (@Bool.rec (fun (_ : Bool) => Level) (level_max_core_subsume fuel a b) a (level_is_zero b)) b (level_is_zero a)) a (fun (x : Level) => levelEqSem x (Level.max a b))
 (fun (_ : @Eq Bool (level_eqb a b) Bool.false) =>
  ugeq_choose_level (level_is_zero a) (@Bool.rec (fun (_ : Bool) => Level) (level_max_core_subsume fuel a b) a (level_is_zero b)) b (fun (x : Level) => levelEqSem x (Level.max a b))
  (fun (_ : @Eq Bool (level_is_zero a) Bool.false) =>
   ugeq_choose_level (level_is_zero b) (level_max_core_subsume fuel a b) a (fun (x : Level) => levelEqSem x (Level.max a b))
   (fun (_ : @Eq Bool (level_is_zero b) Bool.false) => level_max_core_subsume_sound fuel a b)
   (fun (h : @Eq Bool (level_is_zero b) Bool.true) => ugeq_max_return_left a b (ugeq_zero_order a b h)))
  (fun (h : @Eq Bool (level_is_zero a) Bool.true) => ugeq_max_return_right a b (ugeq_zero_order b a h)))
 (fun (h : @Eq Bool (level_eqb a b) Bool.true) => ugeq_max_return_left a b (ugeq_equal_order a b (level_eqb_eq a b h)))",
        "Every raw/fuel smart-max guard preserves max denotation, composing the proved comparator rather than assuming it sound. Not public normalize/is_geq/max correctness.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def ugeq_test_fuel : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))",
        "Concrete eight-layer fuel for nontrivial source-shape controls; not a completeness bound.",
    ),
    (
        r"def ugeq_test_u : Level := Level.param Name.anonymous",
        "First distinct raw universe parameter.",
    ),
    (
        r"def ugeq_test_v : Level := Level.param (Name.str Name.anonymous Nat.zero)",
        "Second distinct raw universe parameter.",
    ),
    (
        r"def ugeq_test_w : Level := Level.param (Name.str Name.anonymous (Nat.succ Nat.zero))",
        "Third distinct raw universe parameter.",
    ),
    (
        r"def ugeq_join_left : Level := Level.max (Level.succ ugeq_test_u) ugeq_test_v",
        "Actual multi-argument dominator for the source join-subsumption shape.",
    ),
    (
        r"def ugeq_join_right : Level := Level.imax (Level.succ ugeq_test_u) (Level.imax (Level.succ ugeq_test_u) ugeq_test_v)",
        "Composite candidate that requires the left-Max-false to right-IMax fallthrough.",
    ),
    (
        r"def ugeq_join_children_refuse :
 @Eq Bool (Bool.or
  (level_geq_core_fuel ugeq_test_fuel (Level.succ ugeq_test_u) ugeq_join_right)
  (level_geq_core_fuel ugeq_test_fuel ugeq_test_v ugeq_join_right)) Bool.false :=
 @Eq.refl Bool Bool.false",
        "Neither single sibling dominates the candidate; replacing production fallthrough with false would lose this valid join.",
    ),
    (
        r"def ugeq_join_comparison :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel ugeq_join_left ugeq_join_right) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Actual computed success that needs the production left-Max failure fallthrough.",
    ),
    (
        r"def ugeq_join_semantic : levelLeqSem ugeq_join_right ugeq_join_left :=
 level_geq_core_fuel_sound ugeq_test_fuel ugeq_join_left ugeq_join_right ugeq_join_comparison",
        "Inhabited universal semantic order produced by the actual fuel-induction theorem and nontrivial computed comparison.",
    ),
    (
        r"def ugeq_join_subsume_left :
 @Eq Level (level_max_core_fuel ugeq_test_fuel ugeq_join_left ugeq_join_right) ugeq_join_left :=
 @Eq.refl Level ugeq_join_left",
        "The first raw comparator arm actually returns the composite join dominator.",
    ),
    (
        r"def ugeq_join_subsume_right :
 @Eq Level (level_max_core_fuel ugeq_test_fuel ugeq_join_right ugeq_join_left) ugeq_join_left :=
 @Eq.refl Level ugeq_join_left",
        "The reverse operand order exercises the second raw comparator arm, not just symmetry in a proof.",
    ),
    (
        r"def ugeq_join_max_caller :
 levelEqSem (level_max_core_fuel ugeq_test_fuel ugeq_join_right ugeq_join_left)
 (Level.max ugeq_join_right ugeq_join_left) :=
 level_max_core_fuel_sound ugeq_test_fuel ugeq_join_right ugeq_join_left",
        "Actual nontrivial subsumption caller composed through the proved smart-max model.",
    ),
    (
        r"def ugeq_fresh_fallback :
 @Eq Level (level_max_core_fuel ugeq_test_fuel ugeq_test_u ugeq_test_v) (Level.max ugeq_test_u ugeq_test_v) :=
 @Eq.refl Level (Level.max ugeq_test_u ugeq_test_v)",
        "Distinct fresh parameters are incomparable to the raw checker; neither subsumption branch fires.",
    ),
    (
        r"def ugeq_fallback_caller :
 levelEqSem (level_max_core_fuel ugeq_test_fuel ugeq_test_u ugeq_test_v) (Level.max ugeq_test_u ugeq_test_v) :=
 level_max_core_fuel_sound ugeq_test_fuel ugeq_test_u ugeq_test_v",
        "Actual fallback caller; a false result never needs to mean semantic non-order.",
    ),
    (
        r"def ugeq_same_base_offset :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Same-base unequal positive exact offsets exercise the reflected numerical guard.",
    ),
    (
        r"def ugeq_equal_offset_recurse :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel (Level.succ (Level.max ugeq_test_u ugeq_test_v)) (Level.succ ugeq_test_u)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Equal positive offsets with different bases actually recurse on the stripped bases.",
    ),
    (
        r"def ugeq_imax_zero_pivot :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel Level.zero (Level.imax (Level.succ ugeq_test_u) Level.zero)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Recursive zero classification accepts a right-IMax at zero without the false iff claiming its left side is also below zero.",
    ),
    (
        r"def ugeq_imax_positive :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel (Level.succ ugeq_test_u) (Level.imax ugeq_test_u (Level.succ ugeq_test_u))) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Both actual RHS-IMax conjunction branches succeed with a definitely positive right child.",
    ),
    (
        r"def ugeq_adversarial_rhs : Level := Level.imax ugeq_test_w ugeq_test_v",
        "Adversarial RHS whose fresh left parameter is not dominated by the candidate join.",
    ),
    (
        r"def ugeq_adversarial_refused :
 @Eq Bool (level_geq_core_fuel ugeq_test_fuel (Level.max ugeq_test_u ugeq_test_v) ugeq_adversarial_rhs) Bool.false :=
 @Eq.refl Bool Bool.false",
        "Actual conjunction refuses an invalid RHS-IMax domination; OR would be unsound.",
    ),
    (
        r"def ugeq_bad_or_would_accept :
 @Eq Bool (Bool.or
  (level_geq_core_fuel ugeq_test_fuel (Level.max ugeq_test_u ugeq_test_v) ugeq_test_w)
  (level_geq_core_fuel ugeq_test_fuel (Level.max ugeq_test_u ugeq_test_v) ugeq_test_v)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "A concrete mutation control: disjunction in place of the RHS conjunction would accept the invalid comparison.",
    ),
    (
        r"def ugeq_counter_valuation (n : Name) : Nat :=
 @Bool.rec (fun (_ : Bool) => Nat)
 (@Bool.rec (fun (_ : Bool) => Nat) (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)
  (name_eqb n (Name.str Name.anonymous Nat.zero)))
 Nat.zero (name_eqb n Name.anonymous)",
        "Actual valuation u=0, v=1, w=2 refutes the invalid OR-based domination.",
    ),
    (
        r"def ugeq_bad_or_semantics_false :
 levelLeqSem ugeq_adversarial_rhs (Level.max ugeq_test_u ugeq_test_v) -> Empty :=
 fun (h : levelLeqSem ugeq_adversarial_rhs (Level.max ugeq_test_u ugeq_test_v)) =>
 le_succ_zero_empty Nat.zero
  (le_succ_le_pred (Nat.succ Nat.zero) (Nat.succ Nat.zero) (h ugeq_counter_valuation))",
        "Constructive refutation at u=0,v=1,w=2: the hypothetical order yields 2<=1 then 1<=0. Not merely a rejected candidate proof.",
    ),
    (
        r"def ugeq_reversed_order_false :
 levelLeqSem (Level.succ ugeq_test_u) ugeq_test_u -> Empty :=
 fun (h : levelLeqSem (Level.succ ugeq_test_u) ugeq_test_u) =>
 le_succ_zero_empty Nat.zero (h (fun (_ : Name) => Nat.zero))",
        "Constructive rejection of reversing the comparator soundness direction, at the zero valuation.",
    ),
    (
        r"def ugeq_zero_fuel_refuses_equal :
 @Eq Bool (level_geq_core_fuel Nat.zero ugeq_test_u ugeq_test_u) Bool.false :=
 @Eq.refl Bool Bool.false",
        "Fuel exhaustion can reject an actually reflexive semantic order; no completeness or false-implies-non-order claim.",
    ),
    (
        r"def ugeq_zero_fuel_order_still_true : levelLeqSem ugeq_test_u ugeq_test_u :=
 levelLeqSem_refl ugeq_test_u",
        "Inhabited counterpart to the zero-fuel refusal explicitly demonstrates the incomplete scope.",
    ),
];

impl Specification {
    /// Requires the exact raw Level vocabulary, kexpr_beq_sound,
    /// univ_poly semantic arithmetic, universe_semantic_bridge, and existing
    /// natural order/addition helpers. No typing or fixed reduction env.
    pub(super) fn add_universe_geq_core(&mut self) -> Result<(), SpecError> {
        for (source, description) in ARITH
            .iter()
            .chain(OFFSET)
            .chain(MODEL)
            .chain(SOUND)
            .chain(MAX_CALLER)
            .chain(CONTROLS)
        {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn raw_universe_geq_and_smart_max_have_checked_proofs_and_controls() {
        let spec = crate::test_utils::build_spec_with_stack();
        for (source, _) in super::ARITH
            .iter()
            .chain(super::OFFSET)
            .chain(super::MODEL)
            .chain(super::SOUND)
            .chain(super::MAX_CALLER)
            .chain(super::CONTROLS)
        {
            let name = source.split_whitespace().nth(1).expect("declaration name");
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered raw universe declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}
