/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Multi-head attention support-bound soundness.

`Crownproof.Sbar` proved, for a SINGLE attention head/query, that the
box-truncated simplex objective `Σ_j g_j p_j` is bounded above by the SBAR /
water-filling dual value `U = λ + Σ μ⁺_j p_hi_j − Σ μ⁻_j p_lo_j`
(`sbar_support_sound`, LP weak duality).

This file composes those per-head certificates through the linear output
projection of a multi-head block.  With `H` heads, head `h` reads out a scalar
`o h` and SBAR gives both an upper bound `U h` and a lower bound `L h` on it
(each itself an instance of `sbar_support_sound`, the lower one applied to the
negated objective).  The heads concatenate and feed a linear projection with
weights `w : Fin H → ℚ`, producing `Σ_h w h * o h`.

The novel content is composing the per-head simplex bounds soundly through that
projection.  We split each projection weight by sign — `w h = wpos h − wneg h`
with `wpos, wneg ≥ 0` — exactly the inner-V corner trick from `Sbar`: a
non-negative weight pairs with the head's UPPER bound, a non-positive weight with
its LOWER bound.  The result is the certified upper bound
`Σ_h (wpos h * U h − wneg h * L h)` on the projected output, with NO LP solved.

The general lemma `proj_split_sound` works for any finite head set; `multihead_support_sound`
wires each head bound to `sbar_support_sound`; and `multihead2_explicit` is the
fully spelled-out `H = 2` instance.
-/
import Crownproof.Sbar
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace Crownproof

/--
**Sign-split projection soundness** (the multi-head composition core).

For any finite head set `heads`, given per-head two-sided bounds
`L h ≤ o h ≤ U h` and a sign-split of the projection weights
`w h = wpos h − wneg h` with `wpos h, wneg h ≥ 0`, the projected output
`Σ_h w h * o h` is bounded above by `Σ_h (wpos h * U h − wneg h * L h)`.

Each term is handled exactly like the inner-V corner of `Sbar`: a non-negative
coefficient `wpos h` multiplies the *upper* head bound `U h`, a non-negative
coefficient `wneg h` multiplies the *lower* head bound `L h` (entering with a
minus sign).  Summing the per-term inequalities gives the projected bound.
-/
theorem proj_split_sound
    {H : Type*} (heads : Finset H)
    (o L U w wpos wneg : H → ℚ)
    (hpos : ∀ h ∈ heads, 0 ≤ wpos h)
    (hneg : ∀ h ∈ heads, 0 ≤ wneg h)
    (hsplit : ∀ h ∈ heads, w h = wpos h - wneg h)
    (hL : ∀ h ∈ heads, L h ≤ o h)
    (hU : ∀ h ∈ heads, o h ≤ U h) :
    (∑ h ∈ heads, w h * o h)
      ≤ ∑ h ∈ heads, (wpos h * U h - wneg h * L h) := by
  apply Finset.sum_le_sum
  intro h hh
  -- per-head: w h * o h = wpos h * o h − wneg h * o h ≤ wpos h * U h − wneg h * L h
  have hup  : wpos h * o h ≤ wpos h * U h :=
    mul_le_mul_of_nonneg_left (hU h hh) (hpos h hh)
  have hlow : wneg h * L h ≤ wneg h * o h :=
    mul_le_mul_of_nonneg_left (hL h hh) (hneg h hh)
  have he : w h * o h = wpos h * o h - wneg h * o h := by
    rw [hsplit h hh]; ring
  rw [he]
  linarith [hup, hlow]

/--
**Multi-head attention support-bound soundness.**

Each head `h` runs SBAR over its own box-truncated simplex on positions
`positions h`, with score/objective `g h`, feasible weighting `p h`, box
`[p_lo h, p_hi h]`, and dual `(lam h, μp h, μm h)` certifying the UPPER value
`U h := lam h + Σ μp h · p_hi h − Σ μm h · p_lo h`.  Symmetrically a dual on the
*negated* objective certifies the LOWER value `L h` (i.e. `−L h` is an SBAR
upper bound for `−g h`):

    Llam h + νp h_j − νm h_j = −g h_j,
    L h := −(Llam h + Σ νp h · p_hi h − Σ νm h · p_lo h).

The head readouts `o h := Σ_j g h_j · p h_j` concatenate and feed a linear
projection `w : Fin H → ℚ`.  Splitting `w` by sign (`w = wpos − wneg`,
`wpos, wneg ≥ 0`) yields the certified upper bound on the projected output

    Σ_h w h * o h  ≤  Σ_h ( wpos h * U h − wneg h * L h ).

Every per-head bound is discharged by `sbar_support_sound`; the composition is
`proj_split_sound`.  No LP is solved at any head, and none in the projection.
-/
theorem multihead_support_sound
    {H J : Type*} (heads : Finset H) (positions : H → Finset J)
    (g p p_lo p_hi : H → J → ℚ)
    -- upper SBAR dual per head
    (μp μm : H → J → ℚ) (lam : H → ℚ)
    -- lower SBAR dual per head (dual of the negated objective)
    (νp νm : H → J → ℚ) (Llam : H → ℚ)
    -- projection + its sign split
    (w wpos wneg : H → ℚ)
    -- per-head SBAR feasibility (upper dual)
    (hμp : ∀ h ∈ heads, ∀ j ∈ positions h, 0 ≤ μp h j)
    (hμm : ∀ h ∈ heads, ∀ j ∈ positions h, 0 ≤ μm h j)
    (hdual : ∀ h ∈ heads, ∀ j ∈ positions h, lam h + μp h j - μm h j = g h j)
    -- per-head SBAR feasibility (lower dual: certifies −g)
    (hνp : ∀ h ∈ heads, ∀ j ∈ positions h, 0 ≤ νp h j)
    (hνm : ∀ h ∈ heads, ∀ j ∈ positions h, 0 ≤ νm h j)
    (hdualL : ∀ h ∈ heads, ∀ j ∈ positions h, Llam h + νp h j - νm h j = -g h j)
    -- per-head simplex feasibility of the actual attention weighting
    (hlo : ∀ h ∈ heads, ∀ j ∈ positions h, p_lo h j ≤ p h j)
    (hhi : ∀ h ∈ heads, ∀ j ∈ positions h, p h j ≤ p_hi h j)
    (hsimplex : ∀ h ∈ heads, ∑ j ∈ positions h, p h j = 1)
    -- projection sign split
    (hpos : ∀ h ∈ heads, 0 ≤ wpos h)
    (hneg : ∀ h ∈ heads, 0 ≤ wneg h)
    (hsplit : ∀ h ∈ heads, w h = wpos h - wneg h) :
    (∑ h ∈ heads,
        w h * (∑ j ∈ positions h, g h j * p h j))
      ≤ ∑ h ∈ heads,
          ( wpos h * (lam h + (∑ j ∈ positions h, μp h j * p_hi h j)
                            - (∑ j ∈ positions h, μm h j * p_lo h j))
          - wneg h * (-(Llam h + (∑ j ∈ positions h, νp h j * p_hi h j)
                                - (∑ j ∈ positions h, νm h j * p_lo h j))) ) := by
  -- Per-head readout and its certified bounds.
  set o : H → ℚ := fun h => ∑ j ∈ positions h, g h j * p h j with ho
  set U : H → ℚ := fun h =>
      lam h + (∑ j ∈ positions h, μp h j * p_hi h j)
            - (∑ j ∈ positions h, μm h j * p_lo h j) with hU
  set L : H → ℚ := fun h =>
      -(Llam h + (∑ j ∈ positions h, νp h j * p_hi h j)
               - (∑ j ∈ positions h, νm h j * p_lo h j)) with hL
  -- Upper bound on each head: direct `sbar_support_sound`.
  have hUbound : ∀ h ∈ heads, o h ≤ U h := by
    intro h hh
    exact sbar_support_sound (positions h) (g h) (p h) (p_lo h) (p_hi h)
      (μp h) (μm h) (lam h)
      (hμp h hh) (hμm h hh) (hlo h hh) (hhi h hh) (hsimplex h hh) (hdual h hh)
  -- Lower bound on each head: `sbar_support_sound` for the NEGATED objective.
  -- It gives  Σ (−g) p ≤ Llam + Σ νp p_hi − Σ νm p_lo = −L h, i.e. L h ≤ o h.
  have hLbound : ∀ h ∈ heads, L h ≤ o h := by
    intro h hh
    have hneg' := sbar_support_sound (positions h)
      (fun j => -g h j) (p h) (p_lo h) (p_hi h) (νp h) (νm h) (Llam h)
      (hνp h hh) (hνm h hh) (hlo h hh) (hhi h hh) (hsimplex h hh) (hdualL h hh)
    -- hneg' : Σ (−g) p ≤ Llam + Σ νp p_hi − Σ νm p_lo
    have hsum : (∑ j ∈ positions h, (fun j => -g h j) j * p h j)
        = -(o h) := by
      rw [ho]; simp only; rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum] at hneg'
    rw [hL]
    linarith [hneg']
  -- Compose through the projection by the sign-split core.
  have := proj_split_sound heads o L U w wpos wneg hpos hneg hsplit hLbound hUbound
  -- Unfold the `set` definitions back into the stated goal.
  simpa only [ho, hU, hL] using this

/-! ### Fully explicit `H = 2` instance

The same statement, with the two heads spelled out concretely (no abstract head
index), to exhibit the general pattern on a closed term. -/

/--
**Two-head explicit instance.**  Heads `0` and `1`, with projection weights
`w0, w1` split as `w0 = wpos0 − wneg0`, `w1 = wpos1 − wneg1`.  Each head's
upper/lower readout bound is an `sbar_support_sound` certificate, and the
projected output `w0·o0 + w1·o1` is bounded above by
`(wpos0·U0 − wneg0·L0) + (wpos1·U1 − wneg1·L1)`.
-/
theorem multihead2_explicit
    {J : Type*} (pos0 pos1 : Finset J)
    (g0 p0 p_lo0 p_hi0 μp0 μm0 νp0 νm0 : J → ℚ) (lam0 Llam0 : ℚ)
    (g1 p1 p_lo1 p_hi1 μp1 μm1 νp1 νm1 : J → ℚ) (lam1 Llam1 : ℚ)
    (w0 wpos0 wneg0 w1 wpos1 wneg1 : ℚ)
    -- head 0 upper dual
    (hμp0 : ∀ j ∈ pos0, 0 ≤ μp0 j) (hμm0 : ∀ j ∈ pos0, 0 ≤ μm0 j)
    (hdual0 : ∀ j ∈ pos0, lam0 + μp0 j - μm0 j = g0 j)
    -- head 0 lower dual
    (hνp0 : ∀ j ∈ pos0, 0 ≤ νp0 j) (hνm0 : ∀ j ∈ pos0, 0 ≤ νm0 j)
    (hdualL0 : ∀ j ∈ pos0, Llam0 + νp0 j - νm0 j = -g0 j)
    -- head 0 simplex
    (hlo0 : ∀ j ∈ pos0, p_lo0 j ≤ p0 j) (hhi0 : ∀ j ∈ pos0, p0 j ≤ p_hi0 j)
    (hsx0 : ∑ j ∈ pos0, p0 j = 1)
    -- head 1 upper dual
    (hμp1 : ∀ j ∈ pos1, 0 ≤ μp1 j) (hμm1 : ∀ j ∈ pos1, 0 ≤ μm1 j)
    (hdual1 : ∀ j ∈ pos1, lam1 + μp1 j - μm1 j = g1 j)
    -- head 1 lower dual
    (hνp1 : ∀ j ∈ pos1, 0 ≤ νp1 j) (hνm1 : ∀ j ∈ pos1, 0 ≤ νm1 j)
    (hdualL1 : ∀ j ∈ pos1, Llam1 + νp1 j - νm1 j = -g1 j)
    -- head 1 simplex
    (hlo1 : ∀ j ∈ pos1, p_lo1 j ≤ p1 j) (hhi1 : ∀ j ∈ pos1, p1 j ≤ p_hi1 j)
    (hsx1 : ∑ j ∈ pos1, p1 j = 1)
    -- sign splits
    (hp0 : 0 ≤ wpos0) (hn0 : 0 ≤ wneg0) (hsp0 : w0 = wpos0 - wneg0)
    (hp1 : 0 ≤ wpos1) (hn1 : 0 ≤ wneg1) (hsp1 : w1 = wpos1 - wneg1) :
    w0 * (∑ j ∈ pos0, g0 j * p0 j)
      + w1 * (∑ j ∈ pos1, g1 j * p1 j)
      ≤ ( wpos0 * (lam0 + (∑ j ∈ pos0, μp0 j * p_hi0 j)
                        - (∑ j ∈ pos0, μm0 j * p_lo0 j))
        - wneg0 * (-(Llam0 + (∑ j ∈ pos0, νp0 j * p_hi0 j)
                           - (∑ j ∈ pos0, νm0 j * p_lo0 j))) )
      + ( wpos1 * (lam1 + (∑ j ∈ pos1, μp1 j * p_hi1 j)
                        - (∑ j ∈ pos1, μm1 j * p_lo1 j))
        - wneg1 * (-(Llam1 + (∑ j ∈ pos1, νp1 j * p_hi1 j)
                           - (∑ j ∈ pos1, νm1 j * p_lo1 j))) ) := by
  -- head 0 upper / lower
  have hU0 : (∑ j ∈ pos0, g0 j * p0 j)
      ≤ lam0 + (∑ j ∈ pos0, μp0 j * p_hi0 j) - (∑ j ∈ pos0, μm0 j * p_lo0 j) :=
    sbar_support_sound pos0 g0 p0 p_lo0 p_hi0 μp0 μm0 lam0
      hμp0 hμm0 hlo0 hhi0 hsx0 hdual0
  have hL0' : (∑ j ∈ pos0, (-g0 j) * p0 j)
      ≤ Llam0 + (∑ j ∈ pos0, νp0 j * p_hi0 j) - (∑ j ∈ pos0, νm0 j * p_lo0 j) :=
    sbar_support_sound pos0 (fun j => -g0 j) p0 p_lo0 p_hi0 νp0 νm0 Llam0
      hνp0 hνm0 hlo0 hhi0 hsx0 hdualL0
  have hL0 : (∑ j ∈ pos0, (-g0 j) * p0 j) = -(∑ j ∈ pos0, g0 j * p0 j) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  -- head 1 upper / lower
  have hU1 : (∑ j ∈ pos1, g1 j * p1 j)
      ≤ lam1 + (∑ j ∈ pos1, μp1 j * p_hi1 j) - (∑ j ∈ pos1, μm1 j * p_lo1 j) :=
    sbar_support_sound pos1 g1 p1 p_lo1 p_hi1 μp1 μm1 lam1
      hμp1 hμm1 hlo1 hhi1 hsx1 hdual1
  have hL1' : (∑ j ∈ pos1, (-g1 j) * p1 j)
      ≤ Llam1 + (∑ j ∈ pos1, νp1 j * p_hi1 j) - (∑ j ∈ pos1, νm1 j * p_lo1 j) :=
    sbar_support_sound pos1 (fun j => -g1 j) p1 p_lo1 p_hi1 νp1 νm1 Llam1
      hνp1 hνm1 hlo1 hhi1 hsx1 hdualL1
  have hL1 : (∑ j ∈ pos1, (-g1 j) * p1 j) = -(∑ j ∈ pos1, g1 j * p1 j) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  -- sign-split each projected term and add.
  rw [hL0] at hL0'
  rw [hL1] at hL1'
  have hterm0 :
      w0 * (∑ j ∈ pos0, g0 j * p0 j)
        ≤ wpos0 * (lam0 + (∑ j ∈ pos0, μp0 j * p_hi0 j)
                        - (∑ j ∈ pos0, μm0 j * p_lo0 j))
        - wneg0 * (-(Llam0 + (∑ j ∈ pos0, νp0 j * p_hi0 j)
                           - (∑ j ∈ pos0, νm0 j * p_lo0 j))) := by
    rw [hsp0]
    have h1 := mul_le_mul_of_nonneg_left hU0 hp0
    have h2 := mul_le_mul_of_nonneg_left hL0' hn0
    nlinarith [h1, h2]
  have hterm1 :
      w1 * (∑ j ∈ pos1, g1 j * p1 j)
        ≤ wpos1 * (lam1 + (∑ j ∈ pos1, μp1 j * p_hi1 j)
                        - (∑ j ∈ pos1, μm1 j * p_lo1 j))
        - wneg1 * (-(Llam1 + (∑ j ∈ pos1, νp1 j * p_hi1 j)
                           - (∑ j ∈ pos1, νm1 j * p_lo1 j))) := by
    rw [hsp1]
    have h1 := mul_le_mul_of_nonneg_left hU1 hp1
    have h2 := mul_le_mul_of_nonneg_left hL1' hn1
    nlinarith [h1, h2]
  linarith [hterm0, hterm1]

/-! Trust-base check: only the three standard logical axioms. -/

#print axioms proj_split_sound
#print axioms multihead_support_sound
#print axioms multihead2_explicit

end Crownproof
