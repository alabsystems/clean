/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Softmax-OPERATOR soundness for CROWN attention relaxations.

`Sbar.lean` bounds the attention OUTPUT via the box-truncated simplex LP dual.
Here we record the complementary, purely simplex/barycentric facts that any
CROWN softmax relaxation relies on: the softmax weights `p` form a probability
vector (`p_j ≥ 0`, `Σ p_j = 1`), so for any value vector `v` the convex
combination `Σ p_j v_j` is sandwiched between `min_j v_j` and `max_j v_j`.

We prove, over ℚ, on a finite position set `J`:
  * monotone upper bound : `(∀ j, v_j ≤ M) → Σ p_j v_j ≤ M`
  * monotone lower bound : `(∀ j, m ≤ v_j) → m ≤ Σ p_j v_j`
  * barycentric bound     : `min_j v_j ≤ Σ p_j v_j ≤ max_j v_j`
all from `p_j ≥ 0` and `Σ p_j = 1` only.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace Crownproof

/--
**Softmax monotone upper bound.**

If every value `v_j` is `≤ M` on the support, then the softmax-weighted average
`Σ_j p_j v_j` is `≤ M`, given the probability-simplex constraints `p_j ≥ 0` and
`Σ_j p_j = 1`.  This is the soundness fact CROWN uses to push an attention
relaxation's per-key upper bound `M` through the convex combination.
-/
theorem softmax_weighted_le
    {J : Type*} (positions : Finset J)
    (p v : J → ℚ) (M : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hub : ∀ j ∈ positions, v j ≤ M) :
    (∑ j ∈ positions, p j * v j) ≤ M := by
  have hstep : (∑ j ∈ positions, p j * v j) ≤ (∑ j ∈ positions, p j * M) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hub j hj) (hp j hj)
  calc (∑ j ∈ positions, p j * v j)
      ≤ (∑ j ∈ positions, p j * M) := hstep
    _ = (∑ j ∈ positions, p j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hsimplex, one_mul]

/--
**Softmax monotone lower bound.**

Dually, if every value `v_j` is `≥ m`, then `Σ_j p_j v_j ≥ m`.
-/
theorem softmax_weighted_ge
    {J : Type*} (positions : Finset J)
    (p v : J → ℚ) (m : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hlb : ∀ j ∈ positions, m ≤ v j) :
    m ≤ (∑ j ∈ positions, p j * v j) := by
  have hstep : (∑ j ∈ positions, p j * m) ≤ (∑ j ∈ positions, p j * v j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hlb j hj) (hp j hj)
  calc m = (∑ j ∈ positions, p j) * m := by rw [hsimplex, one_mul]
    _ = (∑ j ∈ positions, p j * m) := by rw [Finset.sum_mul]
    _ ≤ (∑ j ∈ positions, p j * v j) := hstep

/--
**Barycentric upper bound.**

The softmax-weighted average never exceeds the per-key maximum value on the
support: if `vmax` upper-bounds every `v_j`, then `Σ_j p_j v_j ≤ vmax`.
This is `softmax_weighted_le` packaged as the right half of the barycentric
sandwich; `vmax` is intended to be `max_j v_j`.
-/
theorem softmax_le_max
    {J : Type*} (positions : Finset J)
    (p v : J → ℚ) (vmax : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hmax : ∀ j ∈ positions, v j ≤ vmax) :
    (∑ j ∈ positions, p j * v j) ≤ vmax :=
  softmax_weighted_le positions p v vmax hp hsimplex hmax

/--
**Barycentric lower bound.**

Symmetrically, the average is at least the per-key minimum: if `vmin`
lower-bounds every `v_j`, then `vmin ≤ Σ_j p_j v_j`.  `vmin` is intended to be
`min_j v_j`.
-/
theorem softmax_min_le
    {J : Type*} (positions : Finset J)
    (p v : J → ℚ) (vmin : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hmin : ∀ j ∈ positions, vmin ≤ v j) :
    vmin ≤ (∑ j ∈ positions, p j * v j) :=
  softmax_weighted_ge positions p v vmin hp hsimplex hmin

/--
**Full barycentric sandwich.**

Combining the two halves: any softmax convex combination lies in the interval
`[vmin, vmax]` spanned by the value vector, given the probability-simplex
constraints.  This is the simplex/barycentric soundness lemma underpinning the
attention relaxation — distinct from the LP dual in `Sbar.lean`.
-/
theorem softmax_barycentric
    {J : Type*} (positions : Finset J)
    (p v : J → ℚ) (vmin vmax : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hmin : ∀ j ∈ positions, vmin ≤ v j)
    (hmax : ∀ j ∈ positions, v j ≤ vmax) :
    vmin ≤ (∑ j ∈ positions, p j * v j)
      ∧ (∑ j ∈ positions, p j * v j) ≤ vmax :=
  ⟨softmax_min_le positions p v vmin hp hsimplex hmin,
   softmax_le_max positions p v vmax hp hsimplex hmax⟩

/-! Trust-base check. -/
#print axioms softmax_weighted_le
#print axioms softmax_weighted_ge
#print axioms softmax_le_max
#print axioms softmax_min_le
#print axioms softmax_barycentric

end Crownproof
