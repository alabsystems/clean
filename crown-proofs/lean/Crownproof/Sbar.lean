/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

SBAR attention-relaxation soundness, as LP weak duality over the box-truncated
probability simplex — the same Farkas-duality content that underlies the ReLU
`crown_bridge`, now for self-attention.

A single attention (head, query) reduces (after the exact inner-V corner) to

    maximize  Σ_j g_j p_j   subject to   Σ_j p_j = 1,  p_lo_j ≤ p_j ≤ p_hi_j.

The water-filling dual `(λ, μ⁺, μ⁻)` with `λ + μ⁺_j − μ⁻_j = g_j`, `μ⁺,μ⁻ ≥ 0`
certifies the upper bound `U = λ + Σ μ⁺_j p_hi_j − Σ μ⁻_j p_lo_j` WITHOUT solving
the LP.  This theorem proves that certificate sound for every feasible `p`.
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
**SBAR support-bound soundness** (simplex LP weak duality).

For any feasible attention weighting `p` on the box-truncated simplex over a
finite position set `J`, the objective `Σ g_j p_j` is bounded above by the dual
value `λ + Σ μ⁺_j p_hi_j − Σ μ⁻_j p_lo_j`, given the dual feasibility
`λ + μ⁺_j − μ⁻_j = g_j` and `μ⁺_j, μ⁻_j ≥ 0`.

This is `farkas_to_interval` for self-attention: the SBAR certificate
`(λ, μ⁺, μ⁻)` is exactly a Farkas / entailment certificate, and the proof is the
same non-negative-combination argument.
-/
theorem sbar_support_sound
    {J : Type*} (positions : Finset J)
    (g p p_lo p_hi μp μm : J → ℚ) (lam : ℚ)
    (hμp : ∀ j ∈ positions, 0 ≤ μp j)
    (hμm : ∀ j ∈ positions, 0 ≤ μm j)
    (hlo : ∀ j ∈ positions, p_lo j ≤ p j)
    (hhi : ∀ j ∈ positions, p j ≤ p_hi j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hdual : ∀ j ∈ positions, lam + μp j - μm j = g j) :
    (∑ j ∈ positions, g j * p j)
      ≤ lam + (∑ j ∈ positions, μp j * p_hi j) - (∑ j ∈ positions, μm j * p_lo j) := by
  -- Bound the μ⁺ term above (p_j ≤ p_hi_j) and the −μ⁻ term above (p_j ≥ p_lo_j).
  have hup : (∑ j ∈ positions, μp j * p j) ≤ (∑ j ∈ positions, μp j * p_hi j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hhi j hj) (hμp j hj)
  have hlow : (∑ j ∈ positions, μm j * p_lo j) ≤ (∑ j ∈ positions, μm j * p j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hlo j hj) (hμm j hj)
  -- Rewrite the objective via dual feasibility: g_j = λ + μ⁺_j − μ⁻_j, then split.
  have hrw : (∑ j ∈ positions, g j * p j)
      = lam * (∑ j ∈ positions, p j)
        + (∑ j ∈ positions, μp j * p j)
        - (∑ j ∈ positions, μm j * p j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hdual j hj]; ring
  rw [hrw, hsimplex, mul_one]
  linarith [hup, hlow]

/-! Trust-base check. -/
#print axioms sbar_support_sound

end Crownproof
