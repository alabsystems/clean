/-
  Slack-tolerant Farkas combination  (Phase-2 program, Pillar A).

  The exact-rational CROWN certifier closes a leaf by exhibiting a non-negative
  multiplier vector `μ` with the *exact* identity

      ∀ s, (∑ i, μ i * g i s)  =  -(out s) - c                     (†)

  (this is `Crownproof.farkas_premise_combination`, `Bridge.lean`).  The LP-dual
  multipliers `μ` can have astronomically large numerators/denominators
  (numerators to 18,418 bits on a real ACAS-Xu leaf), which is the exact-rational
  *tractability wall* W1: checking (†) costs `O(premises × magnitude)`.

  This file proves the soundness core that lets the engine trade that bignum
  bitwidth for a bounded, low-bitwidth **slack** charged against a *positive*
  safety margin.  Instead of the exact identity (†) we ask only for the
  one-sided, slack-weakened inequality

      ∀ s valid, -(out s) - c - σ  ≤  (∑ i, μ̃ i * g i s)           (‡)

  for some `σ ≥ 0`.  `slack_farkas` then still concludes `out s ≥ -c - σ`, i.e.
  the verifier proves the *weaker* margin `-c - σ`.  When the true safety
  threshold leaves headroom `> σ`, the weaker margin still decides the property,
  and `σ` can be made small with *low-denominator* rounded multipliers `μ̃`
  (`rounding_slack_bound`), so the bignum magnitude never enters the check.

  Everything is a monotone weakening of the kernel-checked
  `farkas_premise_combination`; the trust base is identical and is reported by
  `#print axioms` at the bottom — it must list only
  `[propext, Classical.choice, Quot.sound]` and never `sorryAx`.

  Soundness note: `slack_farkas` is sound *over the reals* via the same argument
  as the exact rule — `σ` only ever weakens the concluded bound, never tightens
  it, so no rounding can produce a false "verified".
-/

import Crownproof.Bridge
import Mathlib.Tactic.Ring

namespace Crownproof

open Finset

/-! ## 1. The slack-tolerant Farkas combination (the new core). -/

/--
**Slack-tolerant Farkas premise combination.**

Same shape as `farkas_premise_combination`, but the exact certificate identity
`∑ μ i * g i s = -(out s) - c` is relaxed to the one-sided slack inequality

    -(out s) - c - σ ≤ ∑ μ i * g i s         (with σ ≥ 0),  on valid states.

Conclusion: on every valid state, `out s ≥ -c - σ`.

This is a *monotone weakening*: with `σ = 0` and the exact identity it recovers
`farkas_premise_combination` (see `slack_farkas_of_exact`).  The slack only ever
relaxes the concluded margin, so it can never turn an unsound bound into a
"verified" one — soundness is preserved by construction.
-/
theorem slack_farkas
    {S : Type*} {ι : Type*} (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c σ : ℚ)
    (valid : S → Prop)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    (_hσ : 0 ≤ σ)   -- the intended contract (σ ≥ 0); soundness holds regardless
    (hcert : ∀ s, valid s → -(out s) - c - σ ≤ ∑ i ∈ premises, μ i * g i s) :
    ∀ s, valid s → -c - σ ≤ out s := by
  intro s hs
  -- Each term μ i * g i s ≤ 0, so the whole sum ≤ 0.
  have hsum_le : (∑ i ∈ premises, μ i * g i s) ≤ 0 := by
    have hzero : (∑ i ∈ premises, (0 : ℚ)) = 0 := by simp
    calc (∑ i ∈ premises, μ i * g i s)
        ≤ (∑ i ∈ premises, (0 : ℚ)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_nonpos_of_nonneg_of_nonpos (hμ i hi) (hg i hi s hs)
      _ = 0 := hzero
  -- Combine the slack inequality with the sum-nonpositivity.
  have h := hcert s hs
  linarith

/--
`slack_farkas` is a faithful generalisation of `farkas_premise_combination`:
the exact identity with zero slack is the special case `σ = 0`.
-/
theorem slack_farkas_of_exact
    {S : Type*} {ι : Type*} (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c : ℚ)
    (valid : S → Prop)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  have h := slack_farkas premises g out μ c 0 valid hμ hg (le_refl 0)
    (by intro s _; have := hcert s; linarith)
  intro s hs
  have := h s hs
  linarith

/-! ## 2. Rounding error becomes a bounded slack. -/

/--
Single-term rounding bound: if `|a| ≤ ea` and `|b| ≤ eb` then the product `a*b`
is bounded below by `-(ea*eb)`.  (Used per-premise: `a = μ̃ i - μ i` the
rounding error, `b = g i s` the premise value, `ea = ε i`, `eb = P i`.)
-/
theorem neg_mul_bound (a b ea eb : ℚ)
    (ha : |a| ≤ ea) (hb : |b| ≤ eb) : -(ea * eb) ≤ a * b := by
  have hea : 0 ≤ ea := le_trans (abs_nonneg a) ha
  have heb : 0 ≤ eb := le_trans (abs_nonneg b) hb
  have habs : |a * b| ≤ ea * eb := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hea
  have := (abs_le.mp habs).1
  linarith

/--
**Rounding slack bound.**  Let `μ` be the exact multipliers and `μ'` any rounded
replacement with per-coordinate error `|μ' i − μ i| ≤ ε i`, and let `P i`
box-enclose the premise values `|g i s| ≤ P i`.  Then the rounded combination
differs from the exact combination by at most `∑ ε i * P i` *below*:

    (∑ μ i * g i s) − (∑ ε i * P i)  ≤  (∑ μ' i * g i s).

Hence the exact identity `∑ μ i * g i s = -(out s) - c` implies the slack
hypothesis (‡) of `slack_farkas` with `σ = ∑ ε i * P i`, *independent of the
magnitude of the exact multipliers `μ`*.
-/
theorem rounding_slack_bound
    {S : Type*} {ι : Type*} (premises : Finset ι)
    (g : ι → S → ℚ) (μ μ' ε P : ι → ℚ) (s : S)
    (hε : ∀ i ∈ premises, |μ' i - μ i| ≤ ε i)
    (hP : ∀ i ∈ premises, |g i s| ≤ P i) :
    (∑ i ∈ premises, μ i * g i s) - (∑ i ∈ premises, ε i * P i)
      ≤ (∑ i ∈ premises, μ' i * g i s) := by
  -- Per-term: 0 ≤ (μ' i * g i s − μ i * g i s) + ε i * P i.
  have hterm : ∀ i ∈ premises,
      0 ≤ (μ' i * g i s - μ i * g i s) + ε i * P i := by
    intro i hi
    have hb := neg_mul_bound (μ' i - μ i) (g i s) (ε i) (P i) (hε i hi) (hP i hi)
    have hexp : (μ' i - μ i) * g i s = μ' i * g i s - μ i * g i s := by ring
    rw [hexp] at hb
    linarith
  have hsum := Finset.sum_nonneg hterm
  -- Distribute the sum of (a - b) + c over the Finset.
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  linarith

/--
**End-to-end slack rule with rounded multipliers.**  Given an exact Farkas
certificate (the identity `∑ μ i * g i s = -(out s) - c`), any non-negative
rounded multiplier vector `μ'` with error budget `ε` and premise enclosure `P`
proves the slack-weakened margin `out s ≥ -c - σ` with `σ = ∑ ε i * P i`, using
only the *rounded* (low-magnitude) multipliers in the kernel check.
-/
theorem slack_farkas_rounded
    {S : Type*} {ι : Type*} (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ μ' ε P : ι → ℚ) (c : ℚ)
    (valid : S → Prop)
    (hμ' : ∀ i ∈ premises, 0 ≤ μ' i)
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    (hεnn : ∀ i ∈ premises, 0 ≤ ε i)
    (hPnn : ∀ i ∈ premises, 0 ≤ P i)
    (hε : ∀ i ∈ premises, |μ' i - μ i| ≤ ε i)
    (hP : ∀ s, valid s → ∀ i ∈ premises, |g i s| ≤ P i)
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, valid s → -c - (∑ i ∈ premises, ε i * P i) ≤ out s := by
  have hσ : 0 ≤ ∑ i ∈ premises, ε i * P i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hεnn i hi) (hPnn i hi))
  refine slack_farkas premises g out μ' c (∑ i ∈ premises, ε i * P i)
    valid hμ' hg hσ ?_
  intro s hvs
  have hbound := rounding_slack_bound premises g μ μ' ε P s hε (hP s hvs)
  have hid := hcert s
  linarith

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms slack_farkas
#print axioms slack_farkas_of_exact
#print axioms neg_mul_bound
#print axioms rounding_slack_bound
#print axioms slack_farkas_rounded

end Crownproof
