/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

QUANTIZED / FIXED-POINT NETWORK soundness — proof-carrying verification stays
EXACT under quantization.

A real deployment runs a *quantized* network: every value is snapped to a
fixed-point grid with step `delta` by a rounding map `q`.  The only thing the
certifier ever needs to know about `q` is its DEFINING ROUND-OFF BOUND

      |q(x) - x| ≤ delta/2                                   (round-to-nearest)

i.e. the quantizer never moves a value by more than half a grid step.  Over ℚ
this is an EXACT rational statement (delta and the grid are rationals), so the
whole pipeline stays exact and sound — no floating-point slack, no soundness
gap.  This file proves the two facts that make that work:

  (a) `quant_envelope` : from the round-off bound, `q(x)` lies in the EXACT
      rational interval `[x - delta/2, x + delta/2]`.  Equivalently the two
      premises `(x - delta/2) - q(x) ≤ 0` and `q(x) - (x + delta/2) ≤ 0` are
      sound `≤ 0` relaxations of the quantizer — so a quantized value slots
      into the Farkas premise family (`farkas_premise_combination`) like any
      other bounded operation in this project.

  (b) `quant_linear_propagation` : propagating these per-coordinate enclosures
      through a LINEAR layer keeps an exact-rational sound bound.  If the layer
      computes `y_q = Σ w_i * q(x_i)` on the quantized inputs while the ideal
      layer computes `y = Σ w_i * x_i`, then the output error is bounded
      LINEARLY by the accumulation `Σ |w_i| * delta/2`:

          |y_q - y| ≤ (Σ_i |w_i|) * (delta/2).

      The per-coordinate error accumulates linearly and is itself an exact
      rational, so the propagated bound is again a sound interval enclosure of
      the quantized layer around the ideal one — the certifier folds it in
      exactly as it folds every other affine map.

  (c) `quant_premise_sound` : the (a)-enclosures phrased as the project-standard
      `≤ 0` premise family (`Fin 2`), proven sound, so a quantizer drops
      directly into `farkas_premise_combination`.

Everything is over ℚ; arithmetic is exact.  Sorry-free; the trust base is
reported by `#print axioms` at the bottom (only the three standard logical
axioms).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Crownproof

open Finset

/-! ## 1. The quantizer enclosure (round-to-nearest round-off bound).

A quantizer is modelled abstractly by its value `qx` at a point `x` together
with the only property the certifier relies on: the round-off bound
`|qx - x| ≤ delta/2`.  We do not need to know the grid or the rounding rule —
just this exact-rational inequality.  From it we extract the sound interval
enclosure `x - delta/2 ≤ qx ≤ x + delta/2`. -/

/-- **Quantizer interval enclosure.**  From the defining round-off bound
    `|qx - x| ≤ delta/2`, the quantized value `qx` lies in the exact rational
    interval `[x - delta/2, x + delta/2]`.  This is the sound linear interval
    enclosure of the quantizer. -/
theorem quant_envelope (x qx delta : ℚ)
    (hbound : |qx - x| ≤ delta / 2) :
    x - delta / 2 ≤ qx ∧ qx ≤ x + delta / 2 := by
  rw [abs_le] at hbound
  obtain ⟨hlo, hhi⟩ := hbound
  constructor
  · linarith
  · linarith

/-- The lower half of the enclosure as a `≤ 0` premise: `(x - delta/2) - qx ≤ 0`. -/
theorem quant_premise_lo (x qx delta : ℚ)
    (hbound : |qx - x| ≤ delta / 2) :
    (x - delta / 2) - qx ≤ 0 := by
  have := (quant_envelope x qx delta hbound).1; linarith

/-- The upper half of the enclosure as a `≤ 0` premise: `qx - (x + delta/2) ≤ 0`. -/
theorem quant_premise_hi (x qx delta : ℚ)
    (hbound : |qx - x| ≤ delta / 2) :
    qx - (x + delta / 2) ≤ 0 := by
  have := (quant_envelope x qx delta hbound).2; linarith

/-! ## 2. The quantizer as a project-standard `≤ 0` premise family.

We expose the two enclosure halves as a `Fin 2`-indexed premise family on a
state carrying the ideal value `x` and the quantized value `qx`, proven sound,
so a quantizer drops directly into `farkas_premise_combination` exactly like the
box bounds and ReLU envelopes elsewhere in the project. -/

/-- A point-quantization state: the ideal value and its quantized image. -/
structure QState where
  x  : ℚ
  qx : ℚ

/-- `QState.valid delta` holds when the quantization obeys the round-off bound. -/
def QState.valid (delta : ℚ) (st : QState) : Prop :=
  |st.qx - st.x| ≤ delta / 2

/-- The two quantizer premises (`lhs ≤ 0`), indexed by `Fin 2`. -/
def quantPremiseFun (delta : ℚ) : Fin 2 → QState → ℚ
  | 0, st => (st.x - delta / 2) - st.qx     -- lower enclosure
  | 1, st => st.qx - (st.x + delta / 2)     -- upper enclosure

/-- Both quantizer premises are sound `≤ 0` relaxations on valid states.  This is
    the statement that a quantizer is a bounded operation that slots into the
    Farkas premise family. -/
theorem quant_premise_sound (delta : ℚ) :
    ∀ i : Fin 2, ∀ st : QState,
      QState.valid delta st → quantPremiseFun delta i st ≤ 0 := by
  intro i st hv
  fin_cases i
  · exact quant_premise_lo st.x st.qx delta hv
  · exact quant_premise_hi st.x st.qx delta hv

/-! ## 3. Linear-layer propagation of the quantization error.

The ideal layer computes `y = Σ_i w i * x i`; the quantized layer computes
`y_q = Σ_i w i * q(x i)`, where each `q(x i)` obeys the per-coordinate round-off
bound `|q(x i) - x i| ≤ delta/2`.  The output error accumulates LINEARLY:

      |y_q - y| = |Σ_i w i * (q(x i) - x i)| ≤ Σ_i |w i| * (delta/2)
                = (Σ_i |w i|) * (delta/2).

Everything is exact over ℚ, so the propagated bound `(Σ |w i|) * (delta/2)` is an
exact rational and yields a sound interval enclosure of the quantized layer
output around the ideal one. -/

/-- **Per-coordinate linear accumulation.**  For each coordinate the contributed
    error `|w i * (qx i - x i)|` is bounded by `|w i| * (delta/2)`. -/
theorem quant_coord_error_bound (w x qx delta : ℚ)
    (hbound : |qx - x| ≤ delta / 2) :
    |w * (qx - x)| ≤ |w| * (delta / 2) := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg w)

/-- **Quantized linear-layer propagation.**  With per-coordinate round-off bounds
    `|qx i - x i| ≤ delta/2`, the quantized layer output `Σ w i * qx i` differs
    from the ideal output `Σ w i * x i` by at most `(Σ |w i|) * (delta/2)`.  The
    error accumulates linearly and the bound is an exact rational. -/
theorem quant_linear_propagation
    {ι : Type*} (s : Finset ι) (w x qx : ι → ℚ) (delta : ℚ)
    (hbound : ∀ i ∈ s, |qx i - x i| ≤ delta / 2) :
    |(∑ i ∈ s, w i * qx i) - (∑ i ∈ s, w i * x i)|
      ≤ (∑ i ∈ s, |w i|) * (delta / 2) := by
  -- Combine the two sums into a single sum of the per-coordinate differences.
  have hdiff :
      (∑ i ∈ s, w i * qx i) - (∑ i ∈ s, w i * x i)
        = ∑ i ∈ s, w i * (qx i - x i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hdiff]
  -- Triangle inequality, then the per-coordinate bound, then factor out delta/2.
  calc |∑ i ∈ s, w i * (qx i - x i)|
      ≤ ∑ i ∈ s, |w i * (qx i - x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |w i| * (delta / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact quant_coord_error_bound (w i) (x i) (qx i) delta (hbound i hi)
    _ = (∑ i ∈ s, |w i|) * (delta / 2) := by
        rw [← Finset.sum_mul]

/-- **Sound interval enclosure of the quantized linear layer.**  Re-expressing the
    propagation bound as a two-sided interval: the quantized output lies within
    `(Σ |w i|) * (delta/2)` of the ideal output, an exact-rational sound
    enclosure that the certifier folds in like any affine map. -/
theorem quant_linear_enclosure
    {ι : Type*} (s : Finset ι) (w x qx : ι → ℚ) (delta : ℚ)
    (hbound : ∀ i ∈ s, |qx i - x i| ≤ delta / 2) :
    (∑ i ∈ s, w i * x i) - (∑ i ∈ s, |w i|) * (delta / 2)
        ≤ (∑ i ∈ s, w i * qx i) ∧
    (∑ i ∈ s, w i * qx i)
        ≤ (∑ i ∈ s, w i * x i) + (∑ i ∈ s, |w i|) * (delta / 2) := by
  have h := quant_linear_propagation s w x qx delta hbound
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  exact ⟨by linarith, by linarith⟩

/-! ## 4. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms quant_envelope
#print axioms quant_premise_lo
#print axioms quant_premise_hi
#print axioms quant_premise_sound
#print axioms quant_coord_error_bound
#print axioms quant_linear_propagation
#print axioms quant_linear_enclosure

end Crownproof
