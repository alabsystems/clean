/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto3_guaranteed_bound_monotone_in_depth`
(the MONOTONE-TIGHTENING property of input-bisection branch-and-bound).

────────────────────────────────────────────────────────────────────────────
WHAT THE EXISTING DEVELOPMENT GIVES — AND THE GAP THIS FILE FILLS
────────────────────────────────────────────────────────────────────────────
`Complete.complete` (Complete.lean) proves a PURELY EXISTENTIAL fact: SOME finite
bisection depth `d` makes every leaf's relaxed bound strictly positive, hence the
box is decided.  `Complete.leafBoxes_length` (InventionWave2/…C1) counts the
leaves (`= 2^d`).  Neither says ANYTHING about how the per-leaf relaxed-bound
GUARANTEE behaves as the tree deepens — only that a good-enough depth exists.

This file proves the missing QUANTITATIVE, MONOTONE statement.  Define the
*certified guaranteed floor* of a relaxation `R` over root box `B` with positive
root margin `δ ≤ trueMin B` at bisection depth `d`:

      guaranteedFloor R B δ d  :=  δ − L · diam B / 2 ^ d.

Two facts, neither in the existing development nor in Mathlib:

  • SOUNDNESS  (`auto3_floor_le_leaf`):  this floor is a genuine UNIFORM lower
    bound — EVERY depth-`d` leaf `C` has `guaranteedFloor R B δ d ≤ relaxedBound C`.
    (The width-error law, instantiated through the depth-`d` contraction
    `diam C ≤ diam B / 2^d` and the monotonicity `δ ≤ trueMin B ≤ trueMin C`.)

  • MONOTONICITY  (`auto3_guaranteed_bound_monotone_in_depth`, the HEADLINE):  the
    guaranteed floor is NON-DECREASING in depth — going DEEPER never WEAKENS the
    worst-case relaxed-bound guarantee:

        d ≤ d'  ⟹  guaranteedFloor R B δ d ≤ guaranteedFloor R B δ d'.

    Because `L·diam B ≥ 0` and `2^d ≤ 2^d'`, the subtracted error term
    `L·diam B / 2^d` only SHRINKS with depth, so the floor only RISES.  This is
    the formal content of "bisection monotonically tightens the relaxation": the
    branch-and-bound certificate quality improves with effort, and never
    regresses.

This is strictly stronger and more informative than the existential
`exists_decisive_depth`: it exhibits the guarantee as a CONCRETE, MONOTONE,
depth-indexed lower bound — the value-of-information curve of the BaB procedure.

────────────────────────────────────────────────────────────────────────────
WHAT IS REUSED (no new modelling)
────────────────────────────────────────────────────────────────────────────
Everything sits on the LANDED `Complete.Relaxation` structure and its proved
lemmas `Complete.leaf_diam_le` (depth-integrated contraction) and
`Complete.leaf_trueMin_ge` (depth-integrated monotonicity), plus the structure's
own `width_error` / `L_nonneg` / `diam_nonneg`.  No new structure, no new axiom,
no new hypothesis class — the floor is a closed-form function of the existing
data, and both legs are pure order/arithmetic over ℝ.

HONESTY (W-gate, N1).  This is a FIRST FORMALIZATION (N1, pending the
baseline-index novelty check) of the monotone-tightening / value-of-information
property of input-bisection BaB relaxation floors.  The underlying analytic facts
(contraction, width-error) are folklore (Bunel et al., JMLR 2020); the delta is
the EXACT depth-indexed monotone floor and its uniform-soundness pairing, stated
as a sorry-free kernel-checked theorem with axiom closure ⊆ {propext,
Classical.choice, Quot.sound}.  No GPU / wall-clock / solved-instance claim; the
only quantity is a per-depth real-valued certificate floor.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete

namespace Crownproof
namespace InventionWave5

open Crownproof.Complete

variable {Box : Type*} {Sample : Type*} (R : Relaxation Box Sample)

/-! ## 1. The certified guaranteed floor.

`guaranteedFloor R B δ d = δ − L · diam B / 2^d` is the depth-`d` worst-case
lower bound the relaxation certifies for every leaf, given a positive root margin
`δ ≤ trueMin B`.  It is a pure closed form in the existing `Relaxation` data. -/

/-- The certified guaranteed relaxed-bound floor at bisection depth `d`:
`δ − L · diam B / 2^d`. -/
noncomputable def guaranteedFloor (B : Box) (δ : ℝ) (d : ℕ) : ℝ :=
  δ - R.L * R.diam B / 2 ^ d

/-! ## 2. Soundness — the floor is a uniform per-leaf lower bound. -/

/-- **Uniform soundness of the guaranteed floor.**
Given a positive root margin `δ ≤ trueMin B`, EVERY depth-`d` leaf `C` of the
full bisection of `B` has relaxed bound at least the floor:

    guaranteedFloor R B δ d ≤ relaxedBound C.

Combines the structure's `width_error` (`trueMin C − L·diam C ≤ relaxedBound C`)
with the depth-integrated contraction `diam C ≤ diam B / 2^d`
(`leaf_diam_le`) and monotonicity `δ ≤ trueMin B ≤ trueMin C`
(`leaf_trueMin_ge`). -/
theorem auto3_floor_le_leaf (B : Box) {δ : ℝ} (hmin : δ ≤ R.trueMin B) (d : ℕ) :
    ∀ C ∈ leafBoxes R B d, guaranteedFloor R B δ d ≤ R.relaxedBound C := by
  intro C hC
  have hpow : (0:ℝ) < 2 ^ d := by positivity
  -- width-error on the leaf: trueMin C − L·diam C ≤ relaxedBound C
  have hwe : R.trueMin C - R.L * R.diam C ≤ R.relaxedBound C := R.width_error C
  -- depth-d contraction: diam C ≤ diam B / 2^d
  have hdiamC : R.diam C ≤ R.diam B / 2 ^ d := leaf_diam_le R B d C hC
  -- depth-d monotonicity: δ ≤ trueMin B ≤ trueMin C
  have hminC : δ ≤ R.trueMin C := le_trans hmin (leaf_trueMin_ge R B d C hC)
  -- L·diam C ≤ L·(diam B / 2^d) = L·diam B / 2^d  (L ≥ 0)
  have hLdiam : R.L * R.diam C ≤ R.L * R.diam B / 2 ^ d := by
    have h1 : R.L * R.diam C ≤ R.L * (R.diam B / 2 ^ d) :=
      mul_le_mul_of_nonneg_left hdiamC R.L_nonneg
    rwa [mul_div_assoc'] at h1
  -- floor = δ − L·diam B/2^d ≤ trueMin C − L·diam C ≤ relaxedBound C
  unfold guaranteedFloor
  linarith

/-! ## 3. The headline — monotone tightening in depth.

The guaranteed floor only RISES as the tree deepens: the subtracted error term
`L·diam B / 2^d` shrinks because `2^d ≤ 2^d'` and `L·diam B ≥ 0`. -/

/-- **MONOTONE TIGHTENING (HEADLINE).**
The certified guaranteed floor is NON-DECREASING in bisection depth: going deeper
never weakens the worst-case relaxed-bound guarantee.

    d ≤ d'  ⟹  guaranteedFloor R B δ d ≤ guaranteedFloor R B δ d'.

The error term `L·diam B / 2^d` is non-negative (`L ≥ 0`, `diam B ≥ 0`) and
antitone in `d` (its denominator `2^d` grows with `d`), so subtracting it from `δ`
yields a floor that only rises.  This is the formal "value-of-information" /
monotone-tightening property of input-bisection branch-and-bound: certificate
quality improves with effort and never regresses. -/
theorem auto3_guaranteed_bound_monotone_in_depth
    (B : Box) (δ : ℝ) {d d' : ℕ} (hdd : d ≤ d') :
    guaranteedFloor R B δ d ≤ guaranteedFloor R B δ d' := by
  unfold guaranteedFloor
  -- non-negative product L·diam B
  have hLD : 0 ≤ R.L * R.diam B := mul_nonneg R.L_nonneg (R.diam_nonneg B)
  have hpow_d  : (0:ℝ) < 2 ^ d  := by positivity
  have hpow_d' : (0:ℝ) < 2 ^ d' := by positivity
  -- 2^d ≤ 2^d'  (monotone power, base > 1)
  have hpow_le : (2:ℝ) ^ d ≤ 2 ^ d' :=
    pow_le_pow_right₀ (by norm_num) hdd
  -- error at d' ≤ error at d  (larger denominator ⇒ smaller fraction, numerator ≥ 0)
  have herr : R.L * R.diam B / 2 ^ d' ≤ R.L * R.diam B / 2 ^ d :=
    div_le_div_of_nonneg_left hLD hpow_d hpow_le
  -- subtracting a smaller error gives a larger floor
  linarith

/-! ## 4. Consequence — a positive floor decides EVERY leaf, with a monotone certificate.

The two legs combine: if the guaranteed floor is positive at depth `d`, every
depth-`d` leaf's relaxed bound is positive (soundness), and the floor stays
positive at every deeper depth (monotonicity).  So once the certificate floor
turns positive it STAYS positive — the decision, once reached, is stable under
further bisection. -/

/-- **Stable positive decision.**
If the guaranteed floor is strictly positive at depth `d` (given `δ ≤ trueMin B`),
then at EVERY depth `d' ≥ d` every leaf's relaxed bound is strictly positive: the
floor is positive at `d'` (monotonicity) and bounds every depth-`d'` leaf below
(soundness).  The positive verdict, once the floor crosses zero, never reverts
under deeper bisection. -/
theorem auto3_positive_floor_stable
    (B : Box) {δ : ℝ} (hmin : δ ≤ R.trueMin B) {d d' : ℕ} (hdd : d ≤ d')
    (hpos : 0 < guaranteedFloor R B δ d) :
    ∀ C ∈ leafBoxes R B d', 0 < R.relaxedBound C := by
  intro C hC
  -- floor positive at d  ⟹  floor positive at d' ≥ d  (monotonicity)
  have hfloor' : 0 < guaranteedFloor R B δ d' :=
    lt_of_lt_of_le hpos (auto3_guaranteed_bound_monotone_in_depth R B δ hdd)
  -- floor at d' ≤ relaxedBound C  (soundness)
  have hle : guaranteedFloor R B δ d' ≤ R.relaxedBound C :=
    auto3_floor_le_leaf R B hmin d' C hC
  linarith

/-! ## Trust-base check — every theorem must reduce to the standard logical axioms
only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`, NO
`native_decide` / `Lean.ofReduceBool`. -/

#print axioms auto3_floor_le_leaf
#print axioms auto3_guaranteed_bound_monotone_in_depth
#print axioms auto3_positive_floor_stable

end InventionWave5
end Crownproof
