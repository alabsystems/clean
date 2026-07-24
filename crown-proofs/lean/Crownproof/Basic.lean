/-
  CROWN soundness core, formalized in Lean 4 over the rationals (`Rat`),
  using mathlib for ordered-field reasoning.

  These three lemmas are the exact mathematical facts that NY's
  exact-rational CROWN certifier (`crates/ny-cert/src/crown.rs`) relies on:

    1. relu_lower : the lower ReLU envelope  a >= alpha * z  (0 <= alpha <= 1)
                    is a sound lower bound for relu z = max 0 z.
    2. relu_upper : the upper ReLU chord  a <= s*(z - l), s = u/(u-l)
                    is a sound upper bound for relu z on the box [l,u]
                    (with l < 0 < u, the active-instability case).
    3. farkas_comb: a nonneg-weighted (Farkas) combination of valid
                    inequalities  a_i . x <= b_i  entails the combined
                    inequality  (sum mu_i a_i) . x <= sum mu_i b_i.

  We use `relu z := max 0 z`.  All arithmetic is over `Rat`, which is a
  `LinearOrderedField`, so the proofs are pure linear/ordered-field reasoning.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace Crownproof

/-- ReLU on the rationals. -/
def relu (z : ℚ) : ℚ := max 0 z

/-! ## 1. Lower ReLU envelope is sound. -/

/--
For any slope `alpha ∈ [0,1]` and any input `z`, the line `alpha * z`
lies on or below `relu z = max 0 z`.  This is exactly the validity of
CROWN's lower envelope `a >= alpha*z`.
-/
theorem relu_lower (alpha z : ℚ)
    (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    alpha * z ≤ relu z := by
  unfold relu
  rcases le_or_gt 0 z with hz | hz
  · -- z ≥ 0 : relu z = z, and alpha*z ≤ z since (1-alpha) ≥ 0, z ≥ 0.
    have hmax : max 0 z = z := max_eq_right hz
    rw [hmax]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1 - alpha) hz]
  · -- z < 0 : relu z = 0, and alpha*z ≤ 0 since alpha ≥ 0, z < 0.
    have hmax : max 0 z = 0 := max_eq_left (le_of_lt hz)
    rw [hmax]
    exact mul_nonpos_of_nonneg_of_nonpos h0 (le_of_lt hz)

/-! ## 2. Upper ReLU chord is sound on the unstable box [l,u], l < 0 < u. -/

/--
With `l < 0 < u`, the chord through `(l, 0)` and `(u, u)` has slope
`s = u/(u-l)` and value `s*(z - l)`.  For every `z` in the box `[l,u]`,
`relu z = max 0 z ≤ s*(z - l)`.  This is exactly the validity of CROWN's
upper envelope `a <= s*(z - l)`.

We pass `s` explicitly with the defining equation `s * (u - l) = u`
(i.e. `s = u/(u-l)`), keeping the proof division-free and matching the
exact-rational implementation which stores `s` as a `Rat`.
-/
theorem relu_upper (l u s z : ℚ)
    (hl : l < 0) (hu : 0 < u)
    (hs : s * (u - l) = u)        -- s = u/(u-l)
    (hzl : l ≤ z) (hzu : z ≤ u) :
    relu z ≤ s * (z - l) := by
  have hul : 0 < u - l := by linarith
  -- From hs : s*(u-l) = u > 0 and (u-l) > 0  ⇒  s ≥ 0.
  have hs_nonneg : 0 ≤ s := by
    by_contra hneg
    rw [not_le] at hneg
    have hle : s * (u - l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hul)
    rw [hs] at hle
    linarith
  unfold relu
  rcases le_or_gt 0 z with hz | hz
  · -- z ≥ 0 : need z ≤ s*(z - l).
    have hmax : max 0 z = z := max_eq_right hz
    rw [hmax]
    -- Multiply target by (u-l) > 0:  z*(u-l) ≤ (z-l)*u  (using hs),
    -- which reduces to  l*(u - z) ≤ 0  (l<0, u-z≥0).
    have hlu : l * (u - z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hl) (by linarith)
    nlinarith [hs, hul, hlu]
  · -- z < 0 : need 0 ≤ s*(z - l).  s ≥ 0 and (z - l) ≥ 0.
    have hmax : max 0 z = 0 := max_eq_left (le_of_lt hz)
    rw [hmax]
    exact mul_nonneg hs_nonneg (by linarith)

/-! ## 3. Farkas combination of linear inequalities. -/

/--
Two-row Farkas / nonneg-combination step (the inductive building block
of the backward pass).  Given nonneg multipliers `mu1, mu2` and two valid
inequalities `d1 ≤ b1`, `d2 ≤ b2` (where `d_i` are the LHS values
`a_i . x`), the combined inequality holds.
-/
theorem farkas_pair (mu1 mu2 d1 b1 d2 b2 : ℚ)
    (hm1 : 0 ≤ mu1) (hm2 : 0 ≤ mu2)
    (h1 : d1 ≤ b1) (h2 : d2 ≤ b2) :
    mu1 * d1 + mu2 * d2 ≤ mu1 * b1 + mu2 * b2 := by
  have t1 : mu1 * d1 ≤ mu1 * b1 := mul_le_mul_of_nonneg_left h1 hm1
  have t2 : mu2 * d2 ≤ mu2 * b2 := mul_le_mul_of_nonneg_left h2 hm2
  linarith

/--
General `n`-row Farkas combination over lists.  Each row is a triple
`(mu, d, b)`.  Given that every `mu ≥ 0` and every inequality `d ≤ b`
holds, the nonneg-weighted sums satisfy `Σ mu_i d_i ≤ Σ mu_i b_i`.

This is the exact entailment the CROWN backward pass emits: a single
combined inequality dominated by a nonneg combination of the rows.
-/
theorem farkas_comb :
    ∀ (rows : List (ℚ × ℚ × ℚ)),
      (∀ r ∈ rows, 0 ≤ r.1) →                         -- mu ≥ 0
      (∀ r ∈ rows, r.2.1 ≤ r.2.2) →                   -- d ≤ b
      (rows.map (fun r => r.1 * r.2.1)).sum
        ≤ (rows.map (fun r => r.1 * r.2.2)).sum := by
  intro rows
  induction rows with
  | nil => intro _ _; simp
  | cons hd tl ih =>
    intro hmu hdb
    simp only [List.map_cons, List.sum_cons]
    have hmu_hd : 0 ≤ hd.1 := hmu hd (List.mem_cons_self ..)
    have hdb_hd : hd.2.1 ≤ hd.2.2 := hdb hd (List.mem_cons_self ..)
    have hhead : hd.1 * hd.2.1 ≤ hd.1 * hd.2.2 :=
      mul_le_mul_of_nonneg_left hdb_hd hmu_hd
    have htail :
        (tl.map (fun r => r.1 * r.2.1)).sum
          ≤ (tl.map (fun r => r.1 * r.2.2)).sum := by
      apply ih
      · intro r hr; exact hmu r (List.mem_cons_of_mem _ hr)
      · intro r hr; exact hdb r (List.mem_cons_of_mem _ hr)
    linarith

/-! ## Trust-base check.

`#print axioms` lists every axiom each proof depends on.  A genuine
machine-checked proof must NOT list `sorryAx` (which is what `sorry`
elaborates to).  These commands emit the dependency list at build time;
the build log shows only the standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`) and never `sorryAx`. -/

#print axioms relu_lower
#print axioms relu_upper
#print axioms farkas_pair
#print axioms farkas_comb

end Crownproof
