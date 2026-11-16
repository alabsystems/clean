// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stabilization and exact branch equations for the mathematical raw comparator.
//!
//! Positive structural node-count sum bounds every recursive call chain.
//! This proves algorithmic fuel adequacy, not semantic completeness. The raw
//! natural-offset model is still not Rust u32 saturation or public normalize,
//! is_geq or max refinement. No production Rust algorithm is changed.
//!
//! Independent pinned Lean 4.30.0-rc2 check: all 43 new declarations and all
//! 73 imported raw-core declarations have empty axiom closure. Exact PJrAsR
//! export SHA256 4a64c4995ca70fae3c7399eabeaa8e618eeba3cc0f7f65105856ec18086a9571;
//! 90 dependency blocks / 121,178 bytes. Positive check 0.38s, 449,462,272-byte
//! max RSS, 1 GB reservation. Checked slice SHA256:
//! 30ebe33b171c9dfd17ff696e4aaa481253feb7f5dd70d27c2b69e5cb9a46f0ad.
//! Three forged claims (unbounded-fuel equality, lost Max fallthrough and
//! semantic completeness) were rejected at their intended type mismatches.
//! Registered Clean and whole-corpus replay are separate integration gates.
//! See scratch/self-verification-universe-geq-stabilization-2026-09-08.md.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SIZE: &[(&str, &str)] = &[
    (
        r"def level_geq_size (a : Level) : Nat :=
 @Level.rec (fun (_ : Level) => Nat) (Nat.succ Nat.zero)
 (fun (_ : Level) (s : Nat) => Nat.succ s)
 (fun (_ : Level) (_ : Level) (s : Nat) (t : Nat) => Nat.succ (Nat.add s t))
 (fun (_ : Level) (_ : Level) (s : Nat) (t : Nat) => Nat.succ (Nat.add s t))
 (fun (_ : Name) => Nat.succ Nat.zero) a",
        "Positive structural node count of the raw five-constructor universe syntax.",
    ),
    (
        r"def level_geq_bound (a : Level) (b : Level) : Nat := Nat.add (level_geq_size a) (level_geq_size b)",
        "Sum of positive raw tree sizes; sufficient fuel bound, not a semantic-completeness assertion.",
    ),
    (
        r"def ugeq_size_positive (a : Level) : Le (Nat.succ Nat.zero) (level_geq_size a) :=
 @Level.rec (fun (x : Level) => Le (Nat.succ Nat.zero) (level_geq_size x))
 (Le.refl (Nat.succ Nat.zero))
 (fun (x : Level) (ih : Le (Nat.succ Nat.zero) (level_geq_size x)) =>
  Le.step (Nat.succ Nat.zero) (level_geq_size x) ih)
 (fun (x : Level) (y : Level) (_ : Le (Nat.succ Nat.zero) (level_geq_size x)) (_ : Le (Nat.succ Nat.zero) (level_geq_size y)) =>
  le_succ_succ Nat.zero (Nat.add (level_geq_size x) (level_geq_size y)) (le_zero_n (Nat.add (level_geq_size x) (level_geq_size y))))
 (fun (x : Level) (y : Level) (_ : Le (Nat.succ Nat.zero) (level_geq_size x)) (_ : Le (Nat.succ Nat.zero) (level_geq_size y)) =>
  le_succ_succ Nat.zero (Nat.add (level_geq_size x) (level_geq_size y)) (le_zero_n (Nat.add (level_geq_size x) (level_geq_size y))))
 (fun (_ : Name) => Le.refl (Nat.succ Nat.zero)) a",
        "All raw Level trees have at least one node.",
    ),
    (
        r"def ugeq_bound_positive (a : Level) (b : Level) : Le (Nat.succ Nat.zero) (level_geq_bound a b) :=
 le_trans (Nat.succ Nat.zero) (level_geq_size a) (level_geq_bound a b)
 (ugeq_size_positive a) (le_add_self_left (level_geq_size a) (level_geq_size b))",
        "An adequate fuel bound cannot be zero.",
    ),
    (
        r"def ugeq_size_base_le (a : Level) : Le (level_geq_size (level_offset_base a)) (level_geq_size a) :=
 @Level.rec (fun (x : Level) => Le (level_geq_size (level_offset_base x)) (level_geq_size x))
 (Le.refl (Nat.succ Nat.zero))
 (fun (x : Level) (ih : Le (level_geq_size (level_offset_base x)) (level_geq_size x)) =>
  Le.step (level_geq_size (level_offset_base x)) (level_geq_size x) ih)
 (fun (x : Level) (y : Level) (_ : Le (level_geq_size (level_offset_base x)) (level_geq_size x)) (_ : Le (level_geq_size (level_offset_base y)) (level_geq_size y)) =>
  Le.refl (level_geq_size (Level.max x y)))
 (fun (x : Level) (y : Level) (_ : Le (level_geq_size (level_offset_base x)) (level_geq_size x)) (_ : Le (level_geq_size (level_offset_base y)) (level_geq_size y)) =>
  Le.refl (level_geq_size (Level.imax x y)))
 (fun (n : Name) => Le.refl (level_geq_size (Level.param n))) a",
        "Stripping outer successors never increases the exact raw tree size.",
    ),
    (
        r"def ugeq_size_base_lt (a : Level) :
 @Eq Bool (level_offset_positive a) Bool.true ->
 Le (Nat.succ (level_geq_size (level_offset_base a))) (level_geq_size a) :=
 @Level.rec
 (fun (x : Level) => @Eq Bool (level_offset_positive x) Bool.true ->
  Le (Nat.succ (level_geq_size (level_offset_base x))) (level_geq_size x))
 (fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (Le (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) h)
 (fun (x : Level) (_ : @Eq Bool (level_offset_positive x) Bool.true -> Le (Nat.succ (level_geq_size (level_offset_base x))) (level_geq_size x)) =>
  fun (_ : @Eq Bool (level_offset_positive (Level.succ x)) Bool.true) =>
   le_succ_succ (level_geq_size (level_offset_base x)) (level_geq_size x) (ugeq_size_base_le x))
 (fun (x : Level) (y : Level)
 (_ : @Eq Bool (level_offset_positive x) Bool.true -> Le (Nat.succ (level_geq_size (level_offset_base x))) (level_geq_size x))
 (_ : @Eq Bool (level_offset_positive y) Bool.true -> Le (Nat.succ (level_geq_size (level_offset_base y))) (level_geq_size y)) =>
  fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true
   (Le (Nat.succ (level_geq_size (Level.max x y))) (level_geq_size (Level.max x y))) h)
 (fun (x : Level) (y : Level)
 (_ : @Eq Bool (level_offset_positive x) Bool.true -> Le (Nat.succ (level_geq_size (level_offset_base x))) (level_geq_size x))
 (_ : @Eq Bool (level_offset_positive y) Bool.true -> Le (Nat.succ (level_geq_size (level_offset_base y))) (level_geq_size y)) =>
  fun (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true
   (Le (Nat.succ (level_geq_size (Level.imax x y))) (level_geq_size (Level.imax x y))) h)
 (fun (n : Name) (h : @Eq Bool Bool.false Bool.true) => bool_false_ne_true
  (Le (Nat.succ (level_geq_size (Level.param n))) (level_geq_size (Level.param n))) h) a",
        "Actual positive-offset guard implies strict descent to the stripped base. Non-successor cases are refuted by the guard computation.",
    ),
    (
        r"def ugeq_pair_left_lt (a : Level) (small : Level) (b : Level)
 (h : Le (Nat.succ (level_geq_size small)) (level_geq_size a)) :
 Le (Nat.succ (level_geq_bound small b)) (level_geq_bound a b) :=
 Eq.substType Nat (fun (n : Nat) => Le n (level_geq_bound a b))
 (Nat.add (Nat.succ (level_geq_size small)) (level_geq_size b)) (Nat.succ (level_geq_bound small b))
 (nat_succ_add (level_geq_size small) (level_geq_size b))
 (le_add_right_mono (Nat.succ (level_geq_size small)) (level_geq_size a) (level_geq_size b) h)",
        "Strict descent in the first component implies strict descent of the pair bound.",
    ),
    (
        r"def ugeq_pair_right_lt (a : Level) (b : Level) (small : Level)
 (h : Le (Nat.succ (level_geq_size small)) (level_geq_size b)) :
 Le (Nat.succ (level_geq_bound a small)) (level_geq_bound a b) :=
 ugeq_add_left_mono (Nat.succ (level_geq_size small)) (level_geq_size b) (level_geq_size a) h",
        "Strict descent in the second component implies strict descent of the pair bound.",
    ),
    (
        r"def ugeq_pair_bases_lt (a : Level) (b : Level) (h : @Eq Bool (level_offset_positive a) Bool.true) :
 Le (Nat.succ (level_geq_bound (level_offset_base a) (level_offset_base b))) (level_geq_bound a b) :=
 le_trans (Nat.succ (level_geq_bound (level_offset_base a) (level_offset_base b)))
 (level_geq_bound a (level_offset_base b)) (level_geq_bound a b)
 (ugeq_pair_left_lt a (level_offset_base a) (level_offset_base b) (ugeq_size_base_lt a h))
 (ugeq_add_left_mono (level_geq_size (level_offset_base b)) (level_geq_size b) (level_geq_size a) (ugeq_size_base_le b))",
        "The actual recursive equal-positive-offset branch strictly decreases even though both operands are stripped; no normalization premise.",
    ),
    (
        r"def ugeq_binary_left_size (a : Level) (b : Level) :
 Le (Nat.succ (level_geq_size a)) (Nat.succ (Nat.add (level_geq_size a) (level_geq_size b))) :=
 le_succ_succ (level_geq_size a) (Nat.add (level_geq_size a) (level_geq_size b))
 (le_add_self_left (level_geq_size a) (level_geq_size b))",
        "Left child is strictly smaller than either raw binary universe constructor.",
    ),
    (
        r"def ugeq_binary_right_size (a : Level) (b : Level) :
 Le (Nat.succ (level_geq_size b)) (Nat.succ (Nat.add (level_geq_size a) (level_geq_size b))) :=
 le_succ_succ (level_geq_size b) (Nat.add (level_geq_size a) (level_geq_size b))
 (le_add_self_right (level_geq_size a) (level_geq_size b))",
        "Right child is strictly smaller than either raw binary universe constructor.",
    ),
    (
        r"def UGeqSmallerAgree (a : Level) (b : Level) (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) : Prop :=
 forall (x : Level) (y : Level), Le (Nat.succ (level_geq_bound x y)) (level_geq_bound a b) -> @Eq Bool (f x y) (g x y)",
        "Pointwise equality only at strictly smaller pair bounds; used as an induction hypothesis, not a comparator-semantics assumption.",
    ),
    (
        r"def ugeq_choose_congr (guard : Bool) (x : Bool) (x2 : Bool) (y : Bool) (y2 : Bool)
 (hx : @Eq Bool guard Bool.false -> @Eq Bool x x2) (hy : @Eq Bool guard Bool.true -> @Eq Bool y y2) :
 @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y guard) (@Bool.rec (fun (_ : Bool) => Bool) x2 y2 guard) :=
 @Bool.rec
 (fun (q : Bool) => @Eq Bool guard q ->
  @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y q) (@Bool.rec (fun (_ : Bool) => Bool) x2 y2 q))
 hx hy guard (@Eq.refl Bool guard)",
        "Guard-sensitive one-step equality: recursive calls need agreement only when their actual guard is true.",
    ),
];

const CONGR: &[(&str, &str)] = &[
    (
        r"def ugeq_offsets_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level)
 (agree : UGeqSmallerAgree a b f g) : @Eq Bool (level_geq_offsets f a b) (level_geq_offsets g a b) :=
 ugeq_choose_congr (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) (@Bool.rec (fun (_ : Bool) => Bool) Bool.false (f (level_offset_base a) (level_offset_base b)) (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a))) (@Bool.rec (fun (_ : Bool) => Bool) Bool.false (g (level_offset_base a) (level_offset_base b)) (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)))
 (nat_leb (level_offset_nat b) (level_offset_nat a)) (nat_leb (level_offset_nat b) (level_offset_nat a))
 (fun (_ : @Eq Bool (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) Bool.false) =>
  ugeq_choose_congr (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.false Bool.false
   (f (level_offset_base a) (level_offset_base b)) (g (level_offset_base a) (level_offset_base b))
   (fun (_ : @Eq Bool (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.false) => @Eq.refl Bool Bool.false)
   (fun (hg : @Eq Bool (Bool.and (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a)) Bool.true) =>
    agree (level_offset_base a) (level_offset_base b)
     (ugeq_pair_bases_lt a b (band_eq_true_right (nat_eqb (level_offset_nat a) (level_offset_nat b)) (level_offset_positive a) hg))))
 (fun (_ : @Eq Bool (Bool.or (level_eqb (level_offset_base a) (level_offset_base b)) (level_is_zero (level_offset_base b))) Bool.true) => @Eq.refl Bool (nat_leb (level_offset_nat b) (level_offset_nat a)))",
        "Only the actual positive-offset recursive guard invokes smaller-pair agreement; inactive offset branches require no recursive equality.",
    ),
    (
        r"def ugeq_imax_left_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level) :
 UGeqSmallerAgree a b f g -> @Eq Bool (level_geq_imax_left f a b) (level_geq_imax_left g a b) :=
 @Level.rec (fun (z : Level) => UGeqSmallerAgree z b f g -> @Eq Bool (level_geq_imax_left f z b) (level_geq_imax_left g z b))
 (ugeq_offsets_congr f g Level.zero b)
 (fun (x : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) => ugeq_offsets_congr f g (Level.succ x) b)
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) (_ : UGeqSmallerAgree y b f g -> @Eq Bool (level_geq_imax_left f y b) (level_geq_imax_left g y b)) => ugeq_offsets_congr f g (Level.max x y) b)
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_imax_left f x b) (level_geq_imax_left g x b)) (_ : UGeqSmallerAgree y b f g -> @Eq Bool (level_geq_imax_left f y b) (level_geq_imax_left g y b)) => fun (agree : UGeqSmallerAgree (Level.imax x y) b f g) =>
 agree y b (ugeq_pair_left_lt (Level.imax x y) y b (ugeq_binary_right_size x y)))
 (fun (n : Name) => ugeq_offsets_congr f g (Level.param n) b) a",
        "Left-IMax recursive call strictly descends to its actual right child.",
    ),
    (
        r"def ugeq_imax_right_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level) :
 UGeqSmallerAgree a b f g -> @Eq Bool (level_geq_imax_right f a b) (level_geq_imax_right g a b) :=
 @Level.rec (fun (z : Level) => UGeqSmallerAgree a z f g -> @Eq Bool (level_geq_imax_right f a z) (level_geq_imax_right g a z))
 (ugeq_imax_left_congr f g a Level.zero)
 (fun (x : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) => ugeq_imax_left_congr f g a (Level.succ x))
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) (_ : UGeqSmallerAgree a y f g -> @Eq Bool (level_geq_imax_right f a y) (level_geq_imax_right g a y)) => ugeq_imax_left_congr f g a (Level.max x y))
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_imax_right f a x) (level_geq_imax_right g a x)) (_ : UGeqSmallerAgree a y f g -> @Eq Bool (level_geq_imax_right f a y) (level_geq_imax_right g a y)) => fun (agree : UGeqSmallerAgree a (Level.imax x y) f g) =>
 universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.and p q)
 (f a x) (g a x) (f a y) (g a y)
 (agree a x (ugeq_pair_right_lt a (Level.imax x y) x (ugeq_binary_left_size x y)))
 (agree a y (ugeq_pair_right_lt a (Level.imax x y) y (ugeq_binary_right_size x y))))
 (fun (n : Name) => ugeq_imax_left_congr f g a (Level.param n)) b",
        "RHS-IMax keeps its conjunction and compares both actual smaller child pairs.",
    ),
    (
        r"def ugeq_max_left_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level) :
 UGeqSmallerAgree a b f g -> @Eq Bool (level_geq_max_left f a b) (level_geq_max_left g a b) :=
 @Level.rec (fun (z : Level) => UGeqSmallerAgree z b f g -> @Eq Bool (level_geq_max_left f z b) (level_geq_max_left g z b))
 (ugeq_imax_right_congr f g Level.zero b)
 (fun (x : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) => ugeq_imax_right_congr f g (Level.succ x) b)
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) (_ : UGeqSmallerAgree y b f g -> @Eq Bool (level_geq_max_left f y b) (level_geq_max_left g y b)) => fun (agree : UGeqSmallerAgree (Level.max x y) b f g) =>
 universe_bridge_congr2 Bool Bool Bool
 (fun (fallback : Bool) (guard : Bool) => @Bool.rec (fun (_ : Bool) => Bool) fallback Bool.true guard)
 (level_geq_imax_right f (Level.max x y) b) (level_geq_imax_right g (Level.max x y) b)
 (Bool.or (f x b) (f y b)) (Bool.or (g x b) (g y b))
 (ugeq_imax_right_congr f g (Level.max x y) b agree)
 (universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.or p q)
  (f x b) (g x b) (f y b) (g y b)
  (agree x b (ugeq_pair_left_lt (Level.max x y) x b (ugeq_binary_left_size x y)))
  (agree y b (ugeq_pair_left_lt (Level.max x y) y b (ugeq_binary_right_size x y)))))
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree x b f g -> @Eq Bool (level_geq_max_left f x b) (level_geq_max_left g x b)) (_ : UGeqSmallerAgree y b f g -> @Eq Bool (level_geq_max_left f y b) (level_geq_max_left g y b)) => ugeq_imax_right_congr f g (Level.imax x y) b)
 (fun (n : Name) => ugeq_imax_right_congr f g (Level.param n) b) a",
        "The left-Max false branch is preserved as the actual RHS-IMax continuation; equal disjunction and equal fallback imply equal result.",
    ),
    (
        r"def ugeq_max_right_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level) :
 UGeqSmallerAgree a b f g -> @Eq Bool (level_geq_max_right f a b) (level_geq_max_right g a b) :=
 @Level.rec (fun (z : Level) => UGeqSmallerAgree a z f g -> @Eq Bool (level_geq_max_right f a z) (level_geq_max_right g a z))
 (ugeq_max_left_congr f g a Level.zero)
 (fun (x : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) => ugeq_max_left_congr f g a (Level.succ x))
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) (_ : UGeqSmallerAgree a y f g -> @Eq Bool (level_geq_max_right f a y) (level_geq_max_right g a y)) => fun (agree : UGeqSmallerAgree a (Level.max x y) f g) =>
 universe_bridge_congr2 Bool Bool Bool (fun (p : Bool) (q : Bool) => Bool.and p q)
 (f a x) (g a x) (f a y) (g a y)
 (agree a x (ugeq_pair_right_lt a (Level.max x y) x (ugeq_binary_left_size x y)))
 (agree a y (ugeq_pair_right_lt a (Level.max x y) y (ugeq_binary_right_size x y))))
 (fun (x : Level) (y : Level) (_ : UGeqSmallerAgree a x f g -> @Eq Bool (level_geq_max_right f a x) (level_geq_max_right g a x)) (_ : UGeqSmallerAgree a y f g -> @Eq Bool (level_geq_max_right f a y) (level_geq_max_right g a y)) => ugeq_max_left_congr f g a (Level.imax x y))
 (fun (n : Name) => ugeq_max_left_congr f g a (Level.param n)) b",
        "RHS-Max precedes all later cases and both recursive child pairs are strictly smaller.",
    ),
    (
        r"def ugeq_core_step_congr (f : Level -> Level -> Bool) (g : Level -> Level -> Bool) (a : Level) (b : Level)
 (agree : UGeqSmallerAgree a b f g) : @Eq Bool (level_geq_core_step f a b) (level_geq_core_step g a b) :=
 Eq.cong Bool Bool
 (fun (fallback : Bool) => @Bool.rec (fun (_ : Bool) => Bool)
  (@Bool.rec (fun (_ : Bool) => Bool) fallback Bool.true
   (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)))
  Bool.true (Bool.or (level_eqb a b) (level_is_zero b)))
 (level_geq_max_right f a b) (level_geq_max_right g a b)
 (ugeq_max_right_congr f g a b agree)",
        "One exact raw-core layer depends only on strictly smaller pairs; all initial guards and source fallthrough are unchanged.",
    ),
];

const STABLE: &[(&str, &str)] = &[
    (
        r"def ugeq_subfuel_bound (a : Level) (b : Level) (x : Level) (y : Level) (fuel : Nat)
 (small : Le (Nat.succ (level_geq_bound x y)) (level_geq_bound a b))
 (enough : Le (level_geq_bound a b) (Nat.succ fuel)) : Le (level_geq_bound x y) fuel :=
 le_succ_le_pred (level_geq_bound x y) (Nat.succ fuel)
 (le_trans (Nat.succ (level_geq_bound x y)) (level_geq_bound a b) (Nat.succ fuel) small enough)",
        "Strictly smaller recursive pairs fit in predecessor fuel whenever the parent fits in successor fuel.",
    ),
    (
        r"def level_geq_core_fuel_stable (fuel : Nat) : forall (other : Nat) (a : Level) (b : Level),
 Le (level_geq_bound a b) fuel -> Le (level_geq_bound a b) other ->
 @Eq Bool (level_geq_core_fuel fuel a b) (level_geq_core_fuel other a b) :=
 @Nat.rec
 (fun (f : Nat) => forall (g : Nat) (a : Level) (b : Level), Le (level_geq_bound a b) f -> Le (level_geq_bound a b) g ->
 @Eq Bool (level_geq_core_fuel f a b) (level_geq_core_fuel g a b))
 (fun (g : Nat) (a : Level) (b : Level) (hf : Le (level_geq_bound a b) Nat.zero) (_ : Le (level_geq_bound a b) g) =>
  @Empty.rec (fun (_ : Empty) => @Eq Bool (level_geq_core_fuel Nat.zero a b) (level_geq_core_fuel g a b))
   (le_succ_zero_empty Nat.zero
    (le_trans (Nat.succ Nat.zero) (level_geq_bound a b) Nat.zero (ugeq_bound_positive a b) hf)))
 (fun (f : Nat) (ih : forall (g : Nat) (a : Level) (b : Level), Le (level_geq_bound a b) f -> Le (level_geq_bound a b) g ->
 @Eq Bool (level_geq_core_fuel f a b) (level_geq_core_fuel g a b)) =>
  fun (other : Nat) => @Nat.rec
   (fun (g : Nat) => forall (a : Level) (b : Level), Le (level_geq_bound a b) (Nat.succ f) -> Le (level_geq_bound a b) g ->
 @Eq Bool (level_geq_core_fuel (Nat.succ f) a b) (level_geq_core_fuel g a b))
   (fun (a : Level) (b : Level) (_ : Le (level_geq_bound a b) (Nat.succ f)) (hg : Le (level_geq_bound a b) Nat.zero) =>
    @Empty.rec (fun (_ : Empty) => @Eq Bool (level_geq_core_fuel (Nat.succ f) a b) (level_geq_core_fuel Nat.zero a b))
     (le_succ_zero_empty Nat.zero
      (le_trans (Nat.succ Nat.zero) (level_geq_bound a b) Nat.zero (ugeq_bound_positive a b) hg)))
   (fun (g : Nat) (_ : forall (a : Level) (b : Level), Le (level_geq_bound a b) (Nat.succ f) -> Le (level_geq_bound a b) g ->
 @Eq Bool (level_geq_core_fuel (Nat.succ f) a b) (level_geq_core_fuel g a b)) =>
    fun (a : Level) (b : Level) (hf : Le (level_geq_bound a b) (Nat.succ f)) (hg : Le (level_geq_bound a b) (Nat.succ g)) =>
     ugeq_core_step_congr (level_geq_core_fuel f) (level_geq_core_fuel g) a b
      (fun (x : Level) (y : Level) (small : Le (Nat.succ (level_geq_bound x y)) (level_geq_bound a b)) =>
       ih g x y (ugeq_subfuel_bound a b x y f small hf) (ugeq_subfuel_bound a b x y g small hg))) other) fuel",
        "Actual fuel induction proves equality at any two fuels at least size(a)+size(b), using only structural smaller-pair congruence. No semantic-order, completeness or source-normalization premise.",
    ),
    (
        r"def level_geq_core (a : Level) (b : Level) : Bool :=
 level_geq_core_fuel (level_geq_bound a b) a b",
        "Canonical total mathematical natural-offset raw comparator, evaluated at the proved sufficient structural bound.",
    ),
    (
        r"def level_geq_core_fuel_agrees (fuel : Nat) (a : Level) (b : Level)
 (enough : Le (level_geq_bound a b) fuel) :
 @Eq Bool (level_geq_core_fuel fuel a b) (level_geq_core a b) :=
 level_geq_core_fuel_stable fuel (level_geq_bound a b) a b enough (Le.refl (level_geq_bound a b))",
        "Every adequate fuel agrees with the canonical total raw comparator.",
    ),
    (
        r"def level_geq_core_equation (a : Level) (b : Level) :
 @Eq Bool (level_geq_core a b) (level_geq_core_step level_geq_core a b) :=
 Eq.trans Bool (level_geq_core a b)
 (level_geq_core_fuel (Nat.succ (level_geq_bound a b)) a b)
 (level_geq_core_step level_geq_core a b)
 (level_geq_core_fuel_stable (level_geq_bound a b) (Nat.succ (level_geq_bound a b)) a b
  (Le.refl (level_geq_bound a b)) (Le.step (level_geq_bound a b) (level_geq_bound a b) (Le.refl (level_geq_bound a b))))
 (ugeq_core_step_congr (level_geq_core_fuel (level_geq_bound a b)) level_geq_core a b
  (fun (x : Level) (y : Level) (small : Le (Nat.succ (level_geq_bound x y)) (level_geq_bound a b)) =>
   level_geq_core_fuel_stable (level_geq_bound a b) (level_geq_bound x y) x y
    (le_trans (level_geq_bound x y) (Nat.succ (level_geq_bound x y)) (level_geq_bound a b)
     (Le.step (level_geq_bound x y) (level_geq_bound x y) (Le.refl (level_geq_bound x y))) small)
    (Le.refl (level_geq_bound x y))))",
        "The canonical comparator satisfies the exact checked raw-core one-layer branch equation with recursive calls to itself. Derived by stabilization and strict-call congruence, not assumed recursively.",
    ),
    (
        r"def level_geq_core_sound (a : Level) (b : Level)
 (h : @Eq Bool (level_geq_core a b) Bool.true) : levelLeqSem b a :=
 level_geq_core_fuel_sound (level_geq_bound a b) a b h",
        "One-way semantic soundness of the canonical total mathematical raw comparator, composed from the existing universal fuel proof.",
    ),
    (
        r"def ugeq_choose_false (guard : Bool) (x : Bool) (y : Bool) (h : @Eq Bool guard Bool.false) :
 @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y guard) x :=
 Eq.cong Bool Bool (fun (q : Bool) => @Bool.rec (fun (_ : Bool) => Bool) x y q) guard Bool.false h",
        "Concrete false guard equation selects the existing branch without changing its continuation.",
    ),
    (
        r"def ugeq_choose_true (guard : Bool) (x : Bool) (y : Bool) (h : @Eq Bool guard Bool.true) :
 @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x y guard) y :=
 Eq.cong Bool Bool (fun (q : Bool) => @Bool.rec (fun (_ : Bool) => Bool) x y q) guard Bool.true h",
        "Concrete true guard equation selects the existing branch.",
    ),
    (
        r"def level_geq_core_fast_equation (a : Level) (b : Level) (h : @Eq Bool (Bool.or (level_eqb a b) (level_is_zero b)) Bool.true) :
 @Eq Bool (level_geq_core a b) Bool.true :=
 Eq.trans Bool (level_geq_core a b) (level_geq_core_step level_geq_core a b) Bool.true
 (level_geq_core_equation a b) (ugeq_choose_true (Bool.or (level_eqb a b) (level_is_zero b)) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right level_geq_core a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true h)",
        "Exact initial equality-or-recursive-zero branch of the total comparator.",
    ),
    (
        r"def level_geq_core_structural_equation (a : Level) (b : Level)
 (hfast : @Eq Bool (Bool.or (level_eqb a b) (level_is_zero b)) Bool.false) (hoff : @Eq Bool (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) Bool.false) :
 @Eq Bool (level_geq_core a b) (level_geq_max_right level_geq_core a b) :=
 Eq.trans Bool (level_geq_core a b) (level_geq_core_step level_geq_core a b) (level_geq_max_right level_geq_core a b)
 (level_geq_core_equation a b)
 (Eq.trans Bool (level_geq_core_step level_geq_core a b) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right level_geq_core a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) (level_geq_max_right level_geq_core a b)
  (ugeq_choose_false (Bool.or (level_eqb a b) (level_is_zero b)) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right level_geq_core a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true hfast)
  (ugeq_choose_false (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) (level_geq_max_right level_geq_core a b) Bool.true hoff))",
        "After the two real fast guards fail, the canonical comparator follows the exact RHS-Max-first structural dispatcher.",
    ),
    (
        r"def level_geq_core_positive_base_equation (a : Level) (b : Level)
 (hfast : @Eq Bool (Bool.or (level_eqb a b) (level_is_zero b)) Bool.false) (hoff : @Eq Bool (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) Bool.true) :
 @Eq Bool (level_geq_core a b) Bool.true :=
 Eq.trans Bool (level_geq_core a b) (level_geq_core_step level_geq_core a b) Bool.true
 (level_geq_core_equation a b)
 (Eq.trans Bool (level_geq_core_step level_geq_core a b) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right level_geq_core a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true
  (ugeq_choose_false (Bool.or (level_eqb a b) (level_is_zero b)) (@Bool.rec (fun (_ : Bool) => Bool) (level_geq_max_right level_geq_core a b) Bool.true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b))) Bool.true hfast)
  (ugeq_choose_true (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) b)) (level_geq_max_right level_geq_core a b) Bool.true hoff))",
        "Exact stripped-base fast success with an actual positive offset, after the first guard fails.",
    ),
    (
        r"def level_geq_core_rhs_max_equation (a : Level) (x : Level) (y : Level)
 (hfast : @Eq Bool (Bool.or (level_eqb a (Level.max x y)) (level_is_zero (Level.max x y))) Bool.false)
 (hoff : @Eq Bool (Bool.and (level_offset_positive a) (level_eqb (level_offset_base a) (Level.max x y))) Bool.false) :
 @Eq Bool (level_geq_core a (Level.max x y)) (Bool.and (level_geq_core a x) (level_geq_core a y)) :=
 level_geq_core_structural_equation a (Level.max x y) hfast hoff",
        "RHS-Max exact recursive conjunction is derived from the canonical branch equation and the genuine fast-guard failures.",
    ),
    (
        r"def level_geq_core_lhs_max_fallthrough (x : Level) (y : Level) (u : Level) (v : Level)
 (hfast : @Eq Bool (Bool.or (level_eqb (Level.max x y) (Level.imax u v)) (level_is_zero (Level.imax u v))) Bool.false)
 (hoff : @Eq Bool (Bool.and (level_offset_positive (Level.max x y)) (level_eqb (level_offset_base (Level.max x y)) (Level.imax u v))) Bool.false)
 (hchildren : @Eq Bool (Bool.or (level_geq_core x (Level.imax u v)) (level_geq_core y (Level.imax u v))) Bool.false) :
 @Eq Bool (level_geq_core (Level.max x y) (Level.imax u v))
 (Bool.and (level_geq_core (Level.max x y) u) (level_geq_core (Level.max x y) v)) :=
 Eq.trans Bool (level_geq_core (Level.max x y) (Level.imax u v)) (level_geq_max_right level_geq_core (Level.max x y) (Level.imax u v))
 (Bool.and (level_geq_core (Level.max x y) u) (level_geq_core (Level.max x y) v))
 (level_geq_core_structural_equation (Level.max x y) (Level.imax u v) hfast hoff)
 (ugeq_choose_false (Bool.or (level_geq_core x (Level.imax u v)) (level_geq_core y (Level.imax u v)))
  (level_geq_imax_right level_geq_core (Level.max x y) (Level.imax u v)) Bool.true hchildren)",
        "The actual production-order corner: failed left-Max children fall through to the RHS-IMax conjunction, not false.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def ugeq_stable_join_true : @Eq Bool (level_geq_core ugeq_join_left ugeq_join_right) Bool.true :=
 @Eq.refl Bool Bool.true",
        "The canonical comparator really accepts the nontrivial join-subsumption source shape.",
    ),
    (
        r"def ugeq_stable_larger_fuel :
 @Eq Bool (level_geq_core_fuel (Nat.add (level_geq_bound ugeq_join_left ugeq_join_right) ugeq_test_fuel) ugeq_join_left ugeq_join_right)
 (level_geq_core ugeq_join_left ugeq_join_right) :=
 level_geq_core_fuel_agrees (Nat.add (level_geq_bound ugeq_join_left ugeq_join_right) ugeq_test_fuel)
 ugeq_join_left ugeq_join_right (le_add_self_left (level_geq_bound ugeq_join_left ugeq_join_right) ugeq_test_fuel)",
        "Actual stabilization caller uses a strictly larger fuel for the nontrivial join comparison.",
    ),
    (
        r"def ugeq_stable_join_semantic : levelLeqSem ugeq_join_right ugeq_join_left :=
 level_geq_core_sound ugeq_join_left ugeq_join_right ugeq_stable_join_true",
        "Canonical total comparator's proved semantic-soundness theorem has an actual successful caller.",
    ),
    (
        r"def ugeq_stable_join_fallthrough :
 @Eq Bool (level_geq_core ugeq_join_left ugeq_join_right)
 (Bool.and (level_geq_core ugeq_join_left (Level.succ ugeq_test_u))
  (level_geq_core ugeq_join_left (Level.imax (Level.succ ugeq_test_u) ugeq_test_v))) :=
 level_geq_core_lhs_max_fallthrough (Level.succ ugeq_test_u) ugeq_test_v
 (Level.succ ugeq_test_u) (Level.imax (Level.succ ugeq_test_u) ugeq_test_v)
 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.false)",
        "Actual nontrivial caller supplies all real false guards and proves the production fallthrough branch equation, not only final semantic order.",
    ),
    (
        r"def ugeq_stable_offset_descent :
 Le (Nat.succ (level_geq_bound
  (level_offset_base (Level.succ (Level.max ugeq_test_u ugeq_test_v)))
  (level_offset_base (Level.succ ugeq_test_u))))
 (level_geq_bound (Level.succ (Level.max ugeq_test_u ugeq_test_v)) (Level.succ ugeq_test_u)) :=
 ugeq_pair_bases_lt (Level.succ (Level.max ugeq_test_u ugeq_test_v)) (Level.succ ugeq_test_u)
 (@Eq.refl Bool Bool.true)",
        "The same positive-offset recursion used in the core has a concrete strictly smaller pair-bound witness.",
    ),
    (
        r"def ugeq_stable_offset_true :
 @Eq Bool (level_geq_core (Level.succ (Level.max ugeq_test_u ugeq_test_v)) (Level.succ ugeq_test_u)) Bool.true :=
 @Eq.refl Bool Bool.true",
        "Canonical comparison actually follows the equal-positive-offset recursion and accepts.",
    ),
    (
        r"def ugeq_stable_small_fuel_refuses :
 @Eq Bool (level_geq_core_fuel (Nat.succ Nat.zero) ugeq_join_left ugeq_join_right) Bool.false :=
 @Eq.refl Bool Bool.false",
        "One fuel layer is insufficient even though the canonical comparator accepts; an unbounded stability statement would be false.",
    ),
    (
        r"def ugeq_stable_incomplete_rhs : Level := Level.imax (Level.succ Level.zero) ugeq_test_u",
        "imax(1,u)=u semantically, but the raw sufficient-rule comparator need not establish u>=imax(1,u).",
    ),
    (
        r"def ugeq_stable_incomplete_refused :
 @Eq Bool (level_geq_core ugeq_test_u ugeq_stable_incomplete_rhs) Bool.false :=
 @Eq.refl Bool Bool.false",
        "The total canonical raw comparator still refuses a semantically valid order; fuel adequacy is not semantic completeness.",
    ),
    (
        r"def ugeq_stable_incomplete_order : levelLeqSem ugeq_stable_incomplete_rhs ugeq_test_u :=
 fun (rho : Name -> Nat) =>
 Eq.substType Nat (fun (n : Nat) => Le n (evalL rho ugeq_test_u))
 (evalL rho ugeq_test_u) (evalL rho ugeq_stable_incomplete_rhs)
 (level_imax_eq_sem (Level.succ Level.zero) ugeq_test_u rho)
 (Le.refl (evalL rho ugeq_test_u))",
        "Actual imax(1,u)=u identity supplies the refused semantic order under every valuation; reuses the checked mathematical imax bridge.",
    ),
    (
        r"def ugeq_stable_semantic_completeness_false :
 (forall (a : Level) (b : Level), levelLeqSem b a -> @Eq Bool (level_geq_core a b) Bool.true) -> Empty :=
 fun (complete : forall (a : Level) (b : Level), levelLeqSem b a -> @Eq Bool (level_geq_core a b) Bool.true) =>
 nat_zero_ne_succ Nat.zero Empty
 (bool_false_ne_true (@Eq Nat Nat.zero (Nat.succ Nat.zero))
  (complete ugeq_test_u ugeq_stable_incomplete_rhs ugeq_stable_incomplete_order))",
        "Constructive refutation of semantic completeness for this canonical raw algorithm, independent of remaining u32/public-normalizer correspondence.",
    ),
];

impl Specification {
    /// Requires universe_geq_core and existing arithmetic/semantic-imax bridge;
    /// does not require typing, admission or a production normalization theorem.
    pub(super) fn add_universe_geq_stabilization(&mut self) -> Result<(), SpecError> {
        for (source, description) in SIZE.iter().chain(CONGR).chain(STABLE).chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn raw_universe_fuel_stabilization_and_branch_equations_are_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for (source, _) in super::SIZE
            .iter()
            .chain(super::CONGR)
            .chain(super::STABLE)
            .chain(super::CONTROLS)
        {
            let name = source.split_whitespace().nth(1).expect("declaration name");
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked raw universe stabilization declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}
