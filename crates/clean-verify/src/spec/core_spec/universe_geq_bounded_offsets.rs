// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symbolic capped-offset bridge for the mathematical raw universe comparator.
//!
//! Every relevant subterm is bounded; children and stripped bases inherit the
//! invariant. Public normalization/intermediate bounds, source execution/cache,
//! structural Rust refinement and Trust compilation are not proved here.
//! The cap is symbolic. Instantiating it with u32::MAX does not by itself prove
//! that source operations or normalized intermediates satisfy the invariant.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const BOUNDS: &[(&str, &str)] = &[
    (
        r"def UOffsetAnd (P : Prop) (Q : Prop) : Prop := forall (C : Prop), (P -> Q -> C) -> C",
        "Prop-valued conjunction used by the recursive every-subterm invariant.",
    ),
    (
        r"def uoffset_and_intro (P : Prop) (Q : Prop) (p : P) (q : Q) : UOffsetAnd P Q :=
 fun (C : Prop) (k : P -> Q -> C) => k p q",
        "Constructs both actual structural-bound obligations.",
    ),
    (
        r"def uoffset_and_left (P : Prop) (Q : Prop) (h : UOffsetAnd P Q) : P :=
 h P (fun (p : P) (_ : Q) => p)",
        "Projects the actual left bound.",
    ),
    (
        r"def uoffset_and_right (P : Prop) (Q : Prop) (h : UOffsetAnd P Q) : Q :=
 h Q (fun (_ : P) (q : Q) => q)",
        "Projects the actual right bound.",
    ),
    (
        r"def LevelOffsetsBounded (cap : Nat) (a : Level) : Prop :=
 @Level.rec (fun (_ : Level) => Prop) (Le Nat.zero cap)
 (fun (x : Level) (inside : Prop) => UOffsetAnd (Le (Nat.succ (level_offset_nat x)) cap) inside)
 (fun (_ : Level) (_ : Level) (left : Prop) (right : Prop) => UOffsetAnd left right)
 (fun (_ : Level) (_ : Level) (left : Prop) (right : Prop) => UOffsetAnd left right)
 (fun (_ : Name) => Le Nat.zero cap) a",
        "Every-subterm offset bound: every successor subtree has exact leading count <=cap, and both Max/IMax children are checked. This is not merely a top-level bound or a normalization invariant.",
    ),
    (
        r"def level_offsets_bound_succ (cap : Nat) (a : Level) (h : LevelOffsetsBounded cap (Level.succ a)) :
 LevelOffsetsBounded cap a :=
 uoffset_and_right (Le (Nat.succ (level_offset_nat a)) cap) (LevelOffsetsBounded cap a) h",
        "Successor subterms inherit the actual recursively stored bound.",
    ),
    (
        r"def level_offsets_bound_max_left (cap : Nat) (a : Level) (b : Level)
 (h : LevelOffsetsBounded cap (Level.max a b)) : LevelOffsetsBounded cap a :=
 uoffset_and_left (LevelOffsetsBounded cap a) (LevelOffsetsBounded cap b) h",
        "Left Max child inherits the invariant.",
    ),
    (
        r"def level_offsets_bound_max_right (cap : Nat) (a : Level) (b : Level)
 (h : LevelOffsetsBounded cap (Level.max a b)) : LevelOffsetsBounded cap b :=
 uoffset_and_right (LevelOffsetsBounded cap a) (LevelOffsetsBounded cap b) h",
        "Right Max child inherits the invariant.",
    ),
    (
        r"def level_offsets_bound_imax_left (cap : Nat) (a : Level) (b : Level)
 (h : LevelOffsetsBounded cap (Level.imax a b)) : LevelOffsetsBounded cap a :=
 uoffset_and_left (LevelOffsetsBounded cap a) (LevelOffsetsBounded cap b) h",
        "Left IMax child inherits the invariant.",
    ),
    (
        r"def level_offsets_bound_imax_right (cap : Nat) (a : Level) (b : Level)
 (h : LevelOffsetsBounded cap (Level.imax a b)) : LevelOffsetsBounded cap b :=
 uoffset_and_right (LevelOffsetsBounded cap a) (LevelOffsetsBounded cap b) h",
        "Right IMax child inherits the invariant.",
    ),
    (
        r"def level_offsets_bound_count (cap : Nat) (a : Level) :
 LevelOffsetsBounded cap a -> Le (level_offset_nat a) cap :=
 @Level.rec (fun (x : Level) => LevelOffsetsBounded cap x -> Le (level_offset_nat x) cap)
 (fun (h : LevelOffsetsBounded cap Level.zero) => h)
 (fun (x : Level) (_ : LevelOffsetsBounded cap x -> Le (level_offset_nat x) cap) =>
  fun (h : LevelOffsetsBounded cap (Level.succ x)) =>
   uoffset_and_left (Le (Nat.succ (level_offset_nat x)) cap) (LevelOffsetsBounded cap x) h)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> Le (level_offset_nat x) cap) (_ : LevelOffsetsBounded cap y -> Le (level_offset_nat y) cap) =>
  fun (_ : LevelOffsetsBounded cap (Level.max x y)) => le_zero_n cap)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> Le (level_offset_nat x) cap) (_ : LevelOffsetsBounded cap y -> Le (level_offset_nat y) cap) =>
  fun (_ : LevelOffsetsBounded cap (Level.imax x y)) => le_zero_n cap)
 (fun (n : Name) (h : LevelOffsetsBounded cap (Level.param n)) => h) a",
        "The every-subterm invariant entails the actual top-level exact offset bound; it is derived, not a result premise.",
    ),
    (
        r"def level_offsets_bound_base (cap : Nat) (a : Level) :
 LevelOffsetsBounded cap a -> LevelOffsetsBounded cap (level_offset_base a) :=
 @Level.rec (fun (x : Level) => LevelOffsetsBounded cap x -> LevelOffsetsBounded cap (level_offset_base x))
 (fun (h : LevelOffsetsBounded cap Level.zero) => h)
 (fun (x : Level) (ih : LevelOffsetsBounded cap x -> LevelOffsetsBounded cap (level_offset_base x)) =>
  fun (h : LevelOffsetsBounded cap (Level.succ x)) => ih (level_offsets_bound_succ cap x h))
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> LevelOffsetsBounded cap (level_offset_base x)) (_ : LevelOffsetsBounded cap y -> LevelOffsetsBounded cap (level_offset_base y)) =>
  fun (h : LevelOffsetsBounded cap (Level.max x y)) => h)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> LevelOffsetsBounded cap (level_offset_base x)) (_ : LevelOffsetsBounded cap y -> LevelOffsetsBounded cap (level_offset_base y)) =>
  fun (h : LevelOffsetsBounded cap (Level.imax x y)) => h)
 (fun (n : Name) (h : LevelOffsetsBounded cap (Level.param n)) => h) a",
        "Stripped bases inherit the full structural invariant, not only their zero leading offset.",
    ),
    (
        r"def ugeq_nat_leb_complete (a : Nat) (b : Nat) (h : Le a b) : @Eq Bool (nat_leb a b) Bool.true :=
 Eq.cong Nat Bool (fun (n : Nat) => nat_is_zero n) (Nat.sub a b) Nat.zero (le_sub_zero a b h)",
        "Existing Le-to-zero-subtraction proof reflects a true comparison guard; no arithmetic oracle.",
    ),
    (
        r"def level_cap_inc (cap : Nat) (n : Nat) : Nat :=
 @Bool.rec (fun (_ : Bool) => Nat) cap (Nat.succ n) (nat_leb (Nat.succ n) cap)",
        "Mathematical saturating increment: if n+1<=cap return n+1, otherwise cap. Cap is symbolic; no Rust integer execution is assumed.",
    ),
    (
        r"def level_cap_inc_below (cap : Nat) (n : Nat) (h : Le (Nat.succ n) cap) :
 @Eq Nat (level_cap_inc cap n) (Nat.succ n) :=
 Eq.cong Bool Nat (fun (q : Bool) => @Bool.rec (fun (_ : Bool) => Nat) cap (Nat.succ n) q)
 (nat_leb (Nat.succ n) cap) Bool.true (ugeq_nat_leb_complete (Nat.succ n) cap h)",
        "An actually proved finite bound makes saturating increment coincide with mathematical successor.",
    ),
    (
        r"def level_cap_inc_saturated (cap : Nat) (n : Nat) (h : @Eq Bool (nat_leb (Nat.succ n) cap) Bool.false) :
 @Eq Nat (level_cap_inc cap n) cap :=
 Eq.cong Bool Nat (fun (q : Bool) => @Bool.rec (fun (_ : Bool) => Nat) cap (Nat.succ n) q)
 (nat_leb (Nat.succ n) cap) Bool.false h",
        "Actual false guard takes the saturating branch.",
    ),
    (
        r"def level_offset_cap (cap : Nat) (a : Level) : Nat :=
 @Level.rec (fun (_ : Level) => Nat) Nat.zero
 (fun (_ : Level) (count : Nat) => level_cap_inc cap count)
 (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => Nat.zero)
 (fun (_ : Level) (_ : Level) (_ : Nat) (_ : Nat) => Nat.zero)
 (fun (_ : Name) => Nat.zero) a",
        "Explicit per-successor saturating count of the leading spine; base extraction remains structural.",
    ),
    (
        r"def level_offset_cap_eq (cap : Nat) (a : Level) :
 LevelOffsetsBounded cap a -> @Eq Nat (level_offset_cap cap a) (level_offset_nat a) :=
 @Level.rec
 (fun (x : Level) => LevelOffsetsBounded cap x -> @Eq Nat (level_offset_cap cap x) (level_offset_nat x))
 (fun (_ : LevelOffsetsBounded cap Level.zero) => @Eq.refl Nat Nat.zero)
 (fun (x : Level) (ih : LevelOffsetsBounded cap x -> @Eq Nat (level_offset_cap cap x) (level_offset_nat x)) =>
  fun (h : LevelOffsetsBounded cap (Level.succ x)) =>
   Eq.trans Nat (level_cap_inc cap (level_offset_cap cap x)) (level_cap_inc cap (level_offset_nat x)) (Nat.succ (level_offset_nat x))
    (Eq.cong Nat Nat (fun (n : Nat) => level_cap_inc cap n) (level_offset_cap cap x) (level_offset_nat x)
     (ih (level_offsets_bound_succ cap x h)))
    (level_cap_inc_below cap (level_offset_nat x)
     (uoffset_and_left (Le (Nat.succ (level_offset_nat x)) cap) (LevelOffsetsBounded cap x) h)))
 (fun (x : Level) (y : Level)
 (_ : LevelOffsetsBounded cap x -> @Eq Nat (level_offset_cap cap x) (level_offset_nat x))
 (_ : LevelOffsetsBounded cap y -> @Eq Nat (level_offset_cap cap y) (level_offset_nat y)) =>
  fun (_ : LevelOffsetsBounded cap (Level.max x y)) => @Eq.refl Nat Nat.zero)
 (fun (x : Level) (y : Level)
 (_ : LevelOffsetsBounded cap x -> @Eq Nat (level_offset_cap cap x) (level_offset_nat x))
 (_ : LevelOffsetsBounded cap y -> @Eq Nat (level_offset_cap cap y) (level_offset_nat y)) =>
  fun (_ : LevelOffsetsBounded cap (Level.imax x y)) => @Eq.refl Nat Nat.zero)
 (fun (n : Name) (_ : LevelOffsetsBounded cap (Level.param n)) => @Eq.refl Nat Nat.zero) a",
        "Actual structural induction proves capped and exact counts coincide under the every-subterm invariant. No output-count equality is assumed.",
    ),
];

const CAPPED: &[(&str, &str)] = &[
    (
        r"def ugeq_count_positive (n : Nat) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false (nat_is_zero n)",
        "Exact >0 guard on the chosen mathematical count.",
    ),
    (
        r"def level_geq_count_offsets (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) Bool.false
   (next (level_offset_base a) (level_offset_base b))
   (Bool.and (nat_eqb ca cb) (ugeq_count_positive ca)))
  (nat_leb cb ca)
  (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b)))",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_imax_left (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_count_offsets ca cb next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_count_offsets ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_count_offsets ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => next y b)
 (fun (_ : Name) => level_geq_count_offsets ca cb next a b) a",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_imax_right (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_count_imax_left ca cb next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_count_imax_left ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_count_imax_left ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => Bool.and (next a x) (next a y))
 (fun (_ : Name) => level_geq_count_imax_left ca cb next a b) b",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_max_left (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_count_imax_right ca cb next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_count_imax_right ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => @Bool.rec (fun (_ : Bool) => Bool) (level_geq_count_imax_right ca cb next a b) Bool.true (Bool.or (next x b) (next y b)))
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_count_imax_right ca cb next a b)
 (fun (_ : Name) => level_geq_count_imax_right ca cb next a b) a",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_max_right (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Level.rec (fun (_ : Level) => Bool)
 (level_geq_count_max_left ca cb next a b)
 (fun (_ : Level) (_ : Bool) => level_geq_count_max_left ca cb next a b)
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => Bool.and (next a x) (next a y))
 (fun (x : Level) (y : Level) (_ : Bool) (_ : Bool) => level_geq_count_max_left ca cb next a b)
 (fun (_ : Name) => level_geq_count_max_left ca cb next a b) b",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_step (ca : Nat) (cb : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_count_max_right ca cb next a b) Bool.true
   (Bool.and (ugeq_count_positive ca) (level_eqb (level_offset_base a) b)))
  Bool.true (Bool.or (level_eqb a b) (level_is_zero b))",
        "Count-parameterized copy of the exact checked raw-core dispatcher; only the two current offset counts vary. Definitionally identified with existing core at Nat counts.",
    ),
    (
        r"def level_geq_count_step_nat (next : Level -> Level -> Bool) (a : Level) (b : Level) :
 @Eq Bool (level_geq_count_step (level_offset_nat a) (level_offset_nat b) next a b) (level_geq_core_step next a b) :=
 @Eq.refl Bool (level_geq_core_step next a b)",
        "Definitional equality verifies the entire count-parameterized guard graph against the existing checked core, including production left-Max false fallthrough.",
    ),
    (
        r"def level_geq_cap_step (cap : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level) : Bool :=
 level_geq_count_step (level_offset_cap cap a) (level_offset_cap cap b) next a b",
        "Actual source-ordered mathematical capped step: every count comparison and positivity guard uses per-successor saturating counts, while structural bases are unchanged.",
    ),
    (
        r"def level_geq_cap_step_nat (cap : Nat) (next : Level -> Level -> Bool) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_cap_step cap next a b) (level_geq_core_step next a b) :=
 Eq.trans Bool (level_geq_cap_step cap next a b)
 (level_geq_count_step (level_offset_nat a) (level_offset_nat b) next a b) (level_geq_core_step next a b)
 (universe_bridge_congr2 Nat Nat Bool (fun (ca : Nat) (cb : Nat) => level_geq_count_step ca cb next a b)
  (level_offset_cap cap a) (level_offset_nat a) (level_offset_cap cap b) (level_offset_nat b)
  (level_offset_cap_eq cap a ha) (level_offset_cap_eq cap b hb))
 (level_geq_count_step_nat next a b)",
        "Whole capped raw-step graph coincides with the Nat-count graph under derived count equality. No comparator-output equality or semantic order is assumed.",
    ),
    (
        r"def level_geq_cap_fuel (cap : Nat) (fuel : Nat) (a : Level) (b : Level) : Bool :=
 @Nat.rec (fun (_ : Nat) => Level -> Level -> Bool)
 (fun (_ : Level) (_ : Level) => Bool.false)
 (fun (_ : Nat) (next : Level -> Level -> Bool) => level_geq_cap_step cap next) fuel a b",
        "Fuel-bounded capped raw comparator with exactly the same recursive control flow, no public normalization.",
    ),
];

const BOUNDED_CONGR: &[(&str, &str)] = &[
    (
        r"def UGeqBoundedAgree (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) : Prop :=
 forall (a : Level) (b : Level), LevelOffsetsBounded cap a -> LevelOffsetsBounded cap b -> @Eq Bool (f a b) (g a b)",
        "Pointwise equality on structurally bounded pairs, used only as the genuine predecessor-fuel induction hypothesis.",
    ),
    (
        r"def ugeq_offsets_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_offsets f a b) (level_geq_offsets g a b) :=
 Eq.cong Bool Bool
 (fun (result : Bool) => @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) Bool.false result
   (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)))
  (nat_leb (level_offset_nat b) (level_offset_nat a))
  (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))))
 (f (level_offset_base a) (level_offset_base b)) (g (level_offset_base a) (level_offset_base b))
 (agree (level_offset_base a) (level_offset_base b)
  (level_offsets_bound_base cap a ha) (level_offsets_bound_base cap b hb))",
        "Both stripped bases inherit every-subterm bounds; the actual offset callback equality is transported through unchanged guards.",
    ),
    (
        r"def ugeq_imax_left_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_imax_left f a b) (level_geq_imax_left g a b) :=
 @Level.rec (fun (z : Level) => LevelOffsetsBounded cap z -> @Eq Bool (level_geq_imax_left f z b) (level_geq_imax_left g z b))
 (fun (h : LevelOffsetsBounded cap Level.zero) => ugeq_offsets_bounded_congr cap f g agree Level.zero b h hb)
 (fun (x : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) => fun (h : LevelOffsetsBounded cap (Level.succ x)) => ugeq_offsets_bounded_congr cap f g agree (Level.succ x) b h hb)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_imax_left f y b) (level_geq_imax_left g y b)) => fun (h : LevelOffsetsBounded cap (Level.max x y)) => ugeq_offsets_bounded_congr cap f g agree (Level.max x y) b h hb)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_imax_left f y b) (level_geq_imax_left g y b)) => fun (h : LevelOffsetsBounded cap (Level.imax x y)) =>
 agree y b (level_offsets_bound_imax_right cap x y h) hb)
 (fun (n : Name) => fun (h : LevelOffsetsBounded cap (Level.param n)) => ugeq_offsets_bounded_congr cap f g agree (Level.param n) b h hb) a ha",
        "Actual raw head dispatcher preserves bounded-next equality using inherited child bounds; no equality is required on unrelated smaller pairs.",
    ),
    (
        r"def ugeq_imax_right_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_imax_right f a b) (level_geq_imax_right g a b) :=
 @Level.rec (fun (z : Level) => LevelOffsetsBounded cap z -> @Eq Bool (level_geq_imax_right f a z) (level_geq_imax_right g a z))
 (fun (h : LevelOffsetsBounded cap Level.zero) => ugeq_imax_left_bounded_congr cap f g agree a Level.zero ha h)
 (fun (x : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) => fun (h : LevelOffsetsBounded cap (Level.succ x)) => ugeq_imax_left_bounded_congr cap f g agree a (Level.succ x) ha h)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_imax_right f a y) (level_geq_imax_right g a y)) => fun (h : LevelOffsetsBounded cap (Level.max x y)) => ugeq_imax_left_bounded_congr cap f g agree a (Level.max x y) ha h)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_imax_right f a y) (level_geq_imax_right g a y)) => fun (h : LevelOffsetsBounded cap (Level.imax x y)) =>
 universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.and p q)
 (f a x) (g a x) (f a y) (g a y)
 (agree a x ha (level_offsets_bound_imax_left cap x y h))
 (agree a y ha (level_offsets_bound_imax_right cap x y h)))
 (fun (n : Name) => fun (h : LevelOffsetsBounded cap (Level.param n)) => ugeq_imax_left_bounded_congr cap f g agree a (Level.param n) ha h) b hb",
        "Actual raw head dispatcher preserves bounded-next equality using inherited child bounds; no equality is required on unrelated smaller pairs.",
    ),
    (
        r"def ugeq_max_left_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_max_left f a b) (level_geq_max_left g a b) :=
 @Level.rec (fun (z : Level) => LevelOffsetsBounded cap z -> @Eq Bool (level_geq_max_left f z b) (level_geq_max_left g z b))
 (fun (h : LevelOffsetsBounded cap Level.zero) => ugeq_imax_right_bounded_congr cap f g agree Level.zero b h hb)
 (fun (x : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) => fun (h : LevelOffsetsBounded cap (Level.succ x)) => ugeq_imax_right_bounded_congr cap f g agree (Level.succ x) b h hb)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_max_left f y b) (level_geq_max_left g y b)) => fun (h : LevelOffsetsBounded cap (Level.max x y)) =>
 universe_bridge_congr2 Bool Bool Bool
 (fun (fallback : Bool) (guard : Bool) => @Bool.rec (fun (_ : Bool) => Bool) fallback Bool.true guard)
 (level_geq_imax_right f (Level.max x y) b) (level_geq_imax_right g (Level.max x y) b)
 (Bool.or (f x b) (f y b)) (Bool.or (g x b) (g y b))
 (ugeq_imax_right_bounded_congr cap f g agree (Level.max x y) b h hb)
 (universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.or p q)
  (f x b) (g x b) (f y b) (g y b)
  (agree x b (level_offsets_bound_max_left cap x y h) hb)
  (agree y b (level_offsets_bound_max_right cap x y h) hb)))
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_max_left f y b) (level_geq_max_left g y b)) => fun (h : LevelOffsetsBounded cap (Level.imax x y)) => ugeq_imax_right_bounded_congr cap f g agree (Level.imax x y) b h hb)
 (fun (n : Name) => fun (h : LevelOffsetsBounded cap (Level.param n)) => ugeq_imax_right_bounded_congr cap f g agree (Level.param n) b h hb) a ha",
        "Actual raw head dispatcher preserves bounded-next equality using inherited child bounds; no equality is required on unrelated smaller pairs.",
    ),
    (
        r"def ugeq_max_right_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_max_right f a b) (level_geq_max_right g a b) :=
 @Level.rec (fun (z : Level) => LevelOffsetsBounded cap z -> @Eq Bool (level_geq_max_right f a z) (level_geq_max_right g a z))
 (fun (h : LevelOffsetsBounded cap Level.zero) => ugeq_max_left_bounded_congr cap f g agree a Level.zero ha h)
 (fun (x : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) => fun (h : LevelOffsetsBounded cap (Level.succ x)) => ugeq_max_left_bounded_congr cap f g agree a (Level.succ x) ha h)
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_max_right f a y) (level_geq_max_right g a y)) => fun (h : LevelOffsetsBounded cap (Level.max x y)) =>
 universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.and p q)
 (f a x) (g a x) (f a y) (g a y)
 (agree a x ha (level_offsets_bound_max_left cap x y h))
 (agree a y ha (level_offsets_bound_max_right cap x y h)))
 (fun (x : Level) (y : Level) (_ : LevelOffsetsBounded cap x -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) (_ : LevelOffsetsBounded cap y -> @Eq Bool (level_geq_max_right f a y) (level_geq_max_right g a y)) => fun (h : LevelOffsetsBounded cap (Level.imax x y)) => ugeq_max_left_bounded_congr cap f g agree a (Level.imax x y) ha h)
 (fun (n : Name) => fun (h : LevelOffsetsBounded cap (Level.param n)) => ugeq_max_left_bounded_congr cap f g agree a (Level.param n) ha h) b hb",
        "Actual raw head dispatcher preserves bounded-next equality using inherited child bounds; no equality is required on unrelated smaller pairs.",
    ),
    (
        r"def ugeq_core_step_bounded_congr (cap : Nat) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool)
 (agree : UGeqBoundedAgree cap f g) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_core_step f a b) (level_geq_core_step g a b) :=
 Eq.cong Bool Bool
 (fun (fallback : Bool) => @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) fallback Bool.true
   (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)))
  Bool.true (Bool.or (level_eqb a b) (level_is_zero b)))
 (level_geq_max_right f a b) (level_geq_max_right g a b)
 (ugeq_max_right_bounded_congr cap f g agree a b ha hb)",
        "One actual raw-core layer preserves predecessor agreement on bounded pairs; all recursive obligations come from child/base inheritance.",
    ),
];

const CORRESPONDENCE: &[(&str, &str)] = &[
    (
        r"def level_geq_cap_fuel_eq (cap : Nat) (fuel : Nat) : forall (a : Level) (b : Level),
 LevelOffsetsBounded cap a -> LevelOffsetsBounded cap b ->
 @Eq Bool (level_geq_cap_fuel cap fuel a b) (level_geq_core_fuel fuel a b) :=
 @Nat.rec
 (fun (f : Nat) => forall (a : Level) (b : Level), LevelOffsetsBounded cap a -> LevelOffsetsBounded cap b ->
  @Eq Bool (level_geq_cap_fuel cap f a b) (level_geq_core_fuel f a b))
 (fun (a : Level) (b : Level) (_ : LevelOffsetsBounded cap a) (_ : LevelOffsetsBounded cap b) =>
  @Eq.refl Bool Bool.false)
 (fun (f : Nat) (ih : forall (a : Level) (b : Level), LevelOffsetsBounded cap a -> LevelOffsetsBounded cap b ->
  @Eq Bool (level_geq_cap_fuel cap f a b) (level_geq_core_fuel f a b)) =>
  fun (a : Level) (b : Level) (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) =>
   Eq.trans Bool
    (level_geq_cap_step cap (level_geq_cap_fuel cap f) a b)
    (level_geq_core_step (level_geq_cap_fuel cap f) a b)
    (level_geq_core_step (level_geq_core_fuel f) a b)
    (level_geq_cap_step_nat cap (level_geq_cap_fuel cap f) a b ha hb)
    (ugeq_core_step_bounded_congr cap (level_geq_cap_fuel cap f) (level_geq_core_fuel f) ih a b ha hb)) fuel",
        "Actual fuel induction composes proved current-count equality with inherited-bound recursive-call equality. The public theorem assumes structural bounds only, never comparator outputs or semantic order.",
    ),
    (
        r"def level_geq_cap_core (cap : Nat) (a : Level) (b : Level) : Bool :=
 level_geq_cap_fuel cap (level_geq_bound a b) a b",
        "Canonical mathematical capped raw comparator uses the same proved sufficient structural fuel; bounds are required for its correspondence theorem.",
    ),
    (
        r"def level_geq_cap_core_eq (cap : Nat) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_cap_core cap a b) (level_geq_core a b) :=
 level_geq_cap_fuel_eq cap (level_geq_bound a b) a b ha hb",
        "Under actual every-subterm bounds the canonical capped and unbounded raw comparators agree, for symbolic cap.",
    ),
    (
        r"def level_geq_cap_fuel_agrees (cap : Nat) (fuel : Nat) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b)
 (enough : Le (level_geq_bound a b) fuel) :
 @Eq Bool (level_geq_cap_fuel cap fuel a b) (level_geq_cap_core cap a b) :=
 Eq.trans Bool (level_geq_cap_fuel cap fuel a b) (level_geq_core_fuel fuel a b) (level_geq_cap_core cap a b)
 (level_geq_cap_fuel_eq cap fuel a b ha hb)
 (Eq.trans Bool (level_geq_core_fuel fuel a b) (level_geq_core a b) (level_geq_cap_core cap a b)
  (level_geq_core_fuel_agrees fuel a b enough)
  (Eq.symm Bool (level_geq_cap_core cap a b) (level_geq_core a b) (level_geq_cap_core_eq cap a b ha hb)))",
        "Capped fuel stabilizes on bounded inputs by actual comparison correspondence and already proved raw stabilization, not by assuming termination or completeness.",
    ),
    (
        r"def level_geq_cap_core_sound (cap : Nat) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b)
 (accepted : @Eq Bool (level_geq_cap_core cap a b) Bool.true) : levelLeqSem b a :=
 level_geq_core_sound a b
 (Eq.trans Bool (level_geq_core a b) (level_geq_cap_core cap a b) Bool.true
  (Eq.symm Bool (level_geq_cap_core cap a b) (level_geq_core a b) (level_geq_cap_core_eq cap a b ha hb)) accepted)",
        "Bounded capped acceptance entails semantic order by the proved full comparator bridge; the cap and every-subterm bounds are explicit.",
    ),
    (
        r"def level_geq_cap_core_equation (cap : Nat) (a : Level) (b : Level)
 (ha : LevelOffsetsBounded cap a) (hb : LevelOffsetsBounded cap b) :
 @Eq Bool (level_geq_cap_core cap a b) (level_geq_cap_step cap (level_geq_cap_core cap) a b) :=
 Eq.trans Bool (level_geq_cap_core cap a b) (level_geq_core a b) (level_geq_cap_step cap (level_geq_cap_core cap) a b)
 (level_geq_cap_core_eq cap a b ha hb)
 (Eq.trans Bool (level_geq_core a b) (level_geq_core_step level_geq_core a b) (level_geq_cap_step cap (level_geq_cap_core cap) a b)
  (level_geq_core_equation a b)
  (Eq.trans Bool (level_geq_core_step level_geq_core a b) (level_geq_core_step (level_geq_cap_core cap) a b) (level_geq_cap_step cap (level_geq_cap_core cap) a b)
   (ugeq_core_step_bounded_congr cap level_geq_core (level_geq_cap_core cap)
    (fun (x : Level) (y : Level) (hx : LevelOffsetsBounded cap x) (hy : LevelOffsetsBounded cap y) =>
     Eq.symm Bool (level_geq_cap_core cap x y) (level_geq_core x y) (level_geq_cap_core_eq cap x y hx hy)) a b ha hb)
   (Eq.symm Bool (level_geq_cap_step cap (level_geq_cap_core cap) a b) (level_geq_core_step (level_geq_cap_core cap) a b)
    (level_geq_cap_step_nat cap (level_geq_cap_core cap) a b ha hb))))",
        "Bounded canonical capped comparator satisfies its actual one-layer source-ordered branch equation, derived through the raw equation and hereditary correspondence.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def ugeq_cap_succ_bound : LevelOffsetsBounded (Nat.succ Nat.zero) (Level.succ ugeq_test_u) :=
 uoffset_and_intro (Le (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_test_u)
 (Le.refl (Nat.succ Nat.zero)) (le_zero_n (Nat.succ Nat.zero))",
        "Positive boundary witness: one successor fits cap one, with the underlying parameter checked.",
    ),
    (
        r"def ugeq_cap_two_bound : LevelOffsetsBounded (Nat.succ (Nat.succ Nat.zero)) (Level.succ (Level.succ ugeq_test_u)) :=
 uoffset_and_intro (Le (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))) (LevelOffsetsBounded (Nat.succ (Nat.succ Nat.zero)) (Level.succ ugeq_test_u))
 (Le.refl (Nat.succ (Nat.succ Nat.zero)))
 (uoffset_and_intro (Le (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero))) (LevelOffsetsBounded (Nat.succ (Nat.succ Nat.zero)) ugeq_test_u)
  (Le.step (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Le.refl (Nat.succ Nat.zero))) (le_zero_n (Nat.succ (Nat.succ Nat.zero))))",
        "Two successors fit cap two; both successor subtrees have explicit actual bounds.",
    ),
    (
        r"def ugeq_cap_nonzero_compare :
 @Eq Bool (level_geq_cap_core (Nat.succ (Nat.succ Nat.zero)) (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Actual canonical capped comparison succeeds at a nonzero, exactly-at-cap offset.",
    ),
    (
        r"def ugeq_cap_nonzero_bridge :
 @Eq Bool (level_geq_cap_core (Nat.succ (Nat.succ Nat.zero)) (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)) (level_geq_core (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)) :=
 level_geq_cap_core_eq (Nat.succ (Nat.succ Nat.zero)) (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)
 ugeq_cap_two_bound (level_offsets_bound_succ (Nat.succ (Nat.succ Nat.zero)) (Level.succ ugeq_test_u) ugeq_cap_two_bound)",
        "Inhabited caller uses the actual whole-comparator theorem at the finite boundary.",
    ),
    (
        r"def ugeq_cap_nonzero_semantic : levelLeqSem (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u)) :=
 level_geq_cap_core_sound (Nat.succ (Nat.succ Nat.zero)) (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)
 ugeq_cap_two_bound (level_offsets_bound_succ (Nat.succ (Nat.succ Nat.zero)) (Level.succ ugeq_test_u) ugeq_cap_two_bound) ugeq_cap_nonzero_compare",
        "Actual accepted comparison is connected to semantic order through the bounded bridge.",
    ),
    (
        r"def ugeq_cap_join_left_bound : LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_join_left :=
 uoffset_and_intro (LevelOffsetsBounded (Nat.succ Nat.zero) (Level.succ ugeq_test_u)) (LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_test_v)
 ugeq_cap_succ_bound (le_zero_n (Nat.succ Nat.zero))",
        "Max fixture proves both actual child bounds, not just its zero leading count.",
    ),
    (
        r"def ugeq_cap_join_right_bound : LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_join_right :=
 uoffset_and_intro (LevelOffsetsBounded (Nat.succ Nat.zero) (Level.succ ugeq_test_u)) (LevelOffsetsBounded (Nat.succ Nat.zero) (Level.imax (Level.succ ugeq_test_u) ugeq_test_v))
 ugeq_cap_succ_bound
 (uoffset_and_intro (LevelOffsetsBounded (Nat.succ Nat.zero) (Level.succ ugeq_test_u)) (LevelOffsetsBounded (Nat.succ Nat.zero) ugeq_test_v) ugeq_cap_succ_bound (le_zero_n (Nat.succ Nat.zero)))",
        "Nested IMax fixture proves every contained successor offset is bounded.",
    ),
    (
        r"def ugeq_cap_join_fallthrough :
 @Eq Bool (level_geq_cap_core (Nat.succ Nat.zero) ugeq_join_left ugeq_join_right) Bool.true :=
 Eq.trans Bool (level_geq_cap_core (Nat.succ Nat.zero) ugeq_join_left ugeq_join_right)
 (level_geq_core ugeq_join_left ugeq_join_right) Bool.true
 (level_geq_cap_core_eq (Nat.succ Nat.zero) ugeq_join_left ugeq_join_right ugeq_cap_join_left_bound ugeq_cap_join_right_bound)
 ugeq_stable_join_true",
        "Actual nontrivial left-Max-false/RHS-IMax success is preserved by the full hereditary bridge, reusing the previously checked fallthrough fixture.",
    ),
    (
        r"def ugeq_cap_boundary_count :
 @Eq Nat (level_offset_cap (Nat.succ Nat.zero) (Level.succ (Level.succ ugeq_test_u))) (Nat.succ Nat.zero) :=
 @Eq.refl Nat (Nat.succ Nat.zero)",
        "At cap one, two actual successor increments saturate to one.",
    ),
    (
        r"def ugeq_cap_boundary_exact_count :
 @Eq Nat (level_offset_nat (Level.succ (Level.succ ugeq_test_u))) (Nat.succ (Nat.succ Nat.zero)) :=
 @Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))",
        "The same raw level has mathematical count two, so saturation cannot be silently identified outside the bound.",
    ),
    (
        r"def ugeq_cap_boundary_accepts :
 @Eq Bool (level_geq_cap_core (Nat.succ Nat.zero) (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Concrete over-limit operand is spuriously accepted by the capped mathematical comparator because the two offsets collide.",
    ),
    (
        r"def ugeq_cap_boundary_raw_refuses :
 @Eq Bool (level_geq_core (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) Bool.false :=
 @Eq.refl Bool Bool.false",
        "The unbounded canonical comparator refuses the same ordered pair.",
    ),
    (
        r"def ugeq_cap_boundary_order_false (h : levelLeqSem (Level.succ (Level.succ ugeq_test_u)) (Level.succ ugeq_test_u)) : Empty :=
 le_succ_zero_empty Nat.zero
 (le_succ_le_pred (Nat.succ Nat.zero) (Nat.succ Nat.zero) (h (fun (_ : Name) => Nat.zero)))",
        "Zero valuation is an explicit semantic counterexample: two is not <= one. No runtime reachability or source exploit claim.",
    ),
    (
        r"def ugeq_cap_boundary_bound_false (h : LevelOffsetsBounded (Nat.succ Nat.zero) (Level.succ (Level.succ ugeq_test_u))) : Empty :=
 le_succ_zero_empty Nat.zero
 (le_succ_le_pred (Nat.succ Nat.zero) (Nat.succ Nat.zero) (level_offsets_bound_count (Nat.succ Nat.zero) (Level.succ (Level.succ ugeq_test_u)) h))",
        "The exact structural invariant correctly excludes the saturating counterexample; nonvacuity controls separately inhabit valid bounds.",
    ),
    (
        r"def ugeq_cap_top_count_still_bounded :
 Le (level_offset_nat (Level.max (Level.succ (Level.succ ugeq_test_u)) ugeq_test_v)) (Nat.succ Nat.zero) :=
 le_zero_n (Nat.succ Nat.zero)",
        "A Max head has zero leading offset despite an over-limit nested successor spine; top-level-only bounds would miss it.",
    ),
    (
        r"def ugeq_cap_hidden_subterm_bound_false
 (h : LevelOffsetsBounded (Nat.succ Nat.zero) (Level.max (Level.succ (Level.succ ugeq_test_u)) ugeq_test_v)) : Empty :=
 ugeq_cap_boundary_bound_false (level_offsets_bound_max_left (Nat.succ Nat.zero) (Level.succ (Level.succ ugeq_test_u)) ugeq_test_v h)",
        "Actual every-subterm invariant rejects the hidden over-limit child even though the outer leading count is in range.",
    ),
    (
        r"def ugeq_cap_unbounded_correspondence_false
 (h : forall (cap : Nat) (a : Level) (b : Level),
  @Eq Bool (level_geq_cap_core cap a b) (level_geq_core a b)) : Empty :=
 nat_zero_ne_succ Nat.zero Empty
 (bool_false_ne_true (@Eq Nat Nat.zero (Nat.succ Nat.zero))
  (Eq.trans Bool Bool.false (level_geq_core (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) Bool.true
   (Eq.symm Bool (level_geq_core (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) Bool.false ugeq_cap_boundary_raw_refuses)
   (Eq.trans Bool (level_geq_core (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) (level_geq_cap_core (Nat.succ Nat.zero) (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) Bool.true
    (Eq.symm Bool (level_geq_cap_core (Nat.succ Nat.zero) (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) (level_geq_core (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))) (h (Nat.succ Nat.zero) (Level.succ ugeq_test_u) (Level.succ (Level.succ ugeq_test_u))))
    ugeq_cap_boundary_accepts)))",
        "Constructively refutes dropping the structural-bound premise from whole-comparator correspondence.",
    ),
];

impl Specification {
    /// Requires the raw comparator and stabilization stages. The only public
    /// correspondence premises are structural bounds on the actual operands.
    pub(super) fn add_universe_geq_bounded_offsets(&mut self) -> Result<(), SpecError> {
        for (source, description) in BOUNDS
            .iter()
            .chain(CAPPED)
            .chain(BOUNDED_CONGR)
            .chain(CORRESPONDENCE)
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
    fn bounded_capped_offsets_match_the_whole_raw_comparator() {
        let spec = crate::test_utils::build_spec_with_stack();
        let mut count = 0;
        for (source, _) in super::BOUNDS
            .iter()
            .chain(super::CAPPED)
            .chain(super::BOUNDED_CONGR)
            .chain(super::CORRESPONDENCE)
            .chain(super::CONTROLS)
        {
            let name = source.split_whitespace().nth(1).expect("declaration name");
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked capped-offset bridge declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
            count += 1;
        }
        assert_eq!(count, 59);
    }
}
