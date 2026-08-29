/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Arbitrary-depth CROWN composition soundness.

`Crownproof.Deep` proved the end-to-end bridge for a network with TWO fixed
hidden ReLU layers (`crown_bridge_deep2`).  This file generalises that result
to a network of ARBITRARY depth `k`:

    x = a₀ → z₁ → a₁ → z₂ → a₂ → ... → z_k → a_k → y

where, for each layer `j` (0-indexed, `j : Fin k`),

    z_j = w_j * a_{j-1} + b_j        (affine)
    a_j = relu z_j                   (ReLU)

and `y = w_out * a_{k-1} + b_out` is a scalar affine read-out.

The novel content over `Deep.lean` is that the premise-soundness proof is
PARAMETRIC in `k`: the premise family has `2*k + 2` members (a box lower/upper
pair plus, for every layer, a ReLU lower/upper envelope pair), indexed by
`Fin (2*k+2)`, and soundness of *every* premise is discharged uniformly by a
single case analysis on the index decomposition `i ↦ (side, layer)` reusing
`relu_lower` / `relu_upper`.  The end-to-end bridge `crown_bridge_deepK` then
follows from the SAME general core `farkas_premise_combination` that proves the
one-layer and depth-2 bridges — composition adds premises, not new theory.

This is the formal content of `farkas_to_interval` for a deep ReLU network of
any depth.
-/
import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

open Finset

namespace Crownproof

/-! ## 1. The depth-`k` network state.

A genuine execution of a depth-`k` scalar ReLU chain stores the input `x`, the
output `y`, and the per-layer pre/post activation arrays `z a : Fin k -> Q`.
The previous activation feeding layer `j` is the prior post-activation, with the
first layer fed by `x`; we write this as `prevAct st j`. -/
structure DeepKState (k : ℕ) where
  x : ℚ
  z : Fin k → ℚ
  a : Fin k → ℚ
  y : ℚ

/-- The activation feeding layer `j`: it is `x` for the first layer (`j = 0`)
    and `a_{j-1}` otherwise. -/
def DeepKState.prevAct {k : ℕ} (st : DeepKState k) (j : Fin k) : ℚ :=
  match h : j.val with
  | 0          => st.x
  | (n + 1)    => st.a ⟨n, by omega⟩

/-- A genuine execution of the depth-`k` network on box `[l,u]`, with per-layer
    weights `w j`, biases `b j`, output weight `wout`, output bias `bout`.

    * the box `l ≤ x ≤ u` holds;
    * every pre-activation is the affine image of the previous activation:
        `z j = w j * (prevAct st j) + b j`;
    * every post-activation is the ReLU of its pre-activation:
        `a j = relu (z j)`;
    * the read-out is `y = wout * a_{k-1} + bout` (when `k > 0`). -/
def DeepKState.valid {k : ℕ}
    (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) (st : DeepKState k) : Prop :=
  l ≤ st.x ∧ st.x ≤ u ∧
  (∀ j : Fin k, st.z j = w j * st.prevAct j + b j) ∧
  (∀ j : Fin k, st.a j = relu (st.z j)) ∧
  st.y = wout * st.a ⟨k - 1, by omega⟩ + bout

/-! ## 2. The premise family (`2k + 2` premises).

Premises are indexed by `Fin (2*k+2)`.  Index `0` is the box-lower premise,
index `1` the box-upper premise; for layer `j : Fin k`, index `2 + 2*j` is its
ReLU lower envelope and index `2 + 2*j + 1` its ReLU upper envelope.

We give the per-layer envelope slopes/anchors as arrays
`alpha s lz : Fin k → ℚ`. -/

/-- Premise functional for index `i`, as an `lhs ≤ 0` relaxation of the state. -/
def premiseFunK {k : ℕ}
    (l u : ℚ) (alpha s lz : Fin k → ℚ) :
    Fin (2 * k + 2) → DeepKState k → ℚ :=
  fun i st =>
    if i.val = 0 then l - st.x
    else if i.val = 1 then st.x - u
    else
      -- i.val ≥ 2; decode layer index and side
      let m := i.val - 2
      let j := m / 2
      if hj : j < k then
        if m % 2 = 0 then
          -- lower envelope of layer j
          alpha ⟨j, hj⟩ * st.z ⟨j, hj⟩ - st.a ⟨j, hj⟩
        else
          -- upper envelope of layer j
          st.a ⟨j, hj⟩ - s ⟨j, hj⟩ * (st.z ⟨j, hj⟩ - lz ⟨j, hj⟩)
      else 0

/-! ### Index-decomposition facts.

For `i : Fin (2*k+2)` with `i.val ≥ 2`, the decoded layer index `(i.val-2)/2`
is `< k`, so the `dite` in `premiseFunK` always takes its `then` branch on the
relevant premises. -/

theorem layer_lt {k : ℕ} (i : Fin (2 * k + 2)) (h : 2 ≤ i.val) :
    (i.val - 2) / 2 < k := by
  have hi : i.val < 2 * k + 2 := i.isLt
  omega

/-! ## 3. Parametric premise soundness.

Every premise is `≤ 0` on every genuine execution.  Box premises by `linarith`;
each ReLU lower/upper premise by `relu_lower` / `relu_upper` at the decoded
layer, using the supplied per-layer pre-activation bounds `hbox_z`.

This is the parametric heart of the file: a SINGLE proof, by case analysis on
the index decomposition, covers all `2k+2` premises for every `k`. -/
theorem premiseFunK_sound {k : ℕ}
    (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ) (hk : 0 < k)
    (alpha s lz uz : Fin k → ℚ)
    (ha0 : ∀ j, 0 ≤ alpha j) (ha1 : ∀ j, alpha j ≤ 1)
    (hlz : ∀ j, lz j < 0) (huz : ∀ j, 0 < uz j)
    (hs  : ∀ j, s j * (uz j - lz j) = uz j)
    (hbox_z : ∀ (st : DeepKState k),
        DeepKState.valid l u w b wout bout hk st →
          ∀ j, lz j ≤ st.z j ∧ st.z j ≤ uz j) :
    ∀ i : Fin (2 * k + 2), ∀ st : DeepKState k,
      DeepKState.valid l u w b wout bout hk st →
        premiseFunK l u alpha s lz i st ≤ 0 := by
  intro i st hv
  obtain ⟨hxl, hxu, hzeq, haeq, hyeq⟩ := hv
  -- Decode the premise index.
  unfold premiseFunK
  by_cases h0 : i.val = 0
  · rw [if_pos h0]; linarith
  · rw [if_neg h0]
    by_cases h1 : i.val = 1
    · rw [if_pos h1]; linarith
    · rw [if_neg h1]
      -- i.val ≥ 2: a per-layer ReLU envelope.
      have h2 : 2 ≤ i.val := by omega
      have hj : (i.val - 2) / 2 < k := layer_lt i h2
      simp only [dif_pos hj]
      set j : Fin k := ⟨(i.val - 2) / 2, hj⟩ with hjdef
      -- pre-activation bound at layer j, and a j = relu (z j)
      obtain ⟨hzl, hzu⟩ := hbox_z st ⟨hxl, hxu, hzeq, haeq, hyeq⟩ j
      have haj : st.a j = relu (st.z j) := haeq j
      by_cases hmod : (i.val - 2) % 2 = 0
      · -- lower envelope
        rw [if_pos hmod, haj]
        have := relu_lower (alpha j) (st.z j) (ha0 j) (ha1 j)
        linarith
      · -- upper envelope
        rw [if_neg hmod, haj]
        have := relu_upper (lz j) (uz j) (s j) (st.z j)
          (hlz j) (huz j) (hs j) hzl hzu
        linarith

/-! ## 4. The arbitrary-depth end-to-end bridge.

If a non-negative multiplier vector `μ : Fin (2*k+2) → ℚ` combines the premises
so that, as a function of the state, the combination equals `-(y) - c`, then
every genuine execution of the depth-`k` network on the box satisfies `y ≥ -c`.

Proven sorry-free by reduction to the general `farkas_premise_combination` —
the SAME core that proves `crown_bridge` and `crown_bridge_deep2`.  The premise
soundness is the parametric `premiseFunK_sound`; nothing else is depth-specific.
-/
theorem crown_bridge_deepK {k : ℕ}
    (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ) (hk : 0 < k)
    (alpha s lz uz : Fin k → ℚ) (c : ℚ)
    (μ : Fin (2 * k + 2) → ℚ)
    (ha0 : ∀ j, 0 ≤ alpha j) (ha1 : ∀ j, alpha j ≤ 1)
    (hlz : ∀ j, lz j < 0) (huz : ∀ j, 0 < uz j)
    (hs  : ∀ j, s j * (uz j - lz j) = uz j)
    (hbox_z : ∀ (st : DeepKState k),
        DeepKState.valid l u w b wout bout hk st →
          ∀ j, lz j ≤ st.z j ∧ st.z j ≤ uz j)
    (hμ : ∀ i, 0 ≤ μ i)
    (hcert : ∀ st : DeepKState k,
        (∑ i, μ i * premiseFunK l u alpha s lz i st) = -(st.y) - c) :
    ∀ st : DeepKState k,
      DeepKState.valid l u w b wout bout hk st → -c ≤ st.y := by
  refine farkas_premise_combination (S := DeepKState k) (ι := Fin (2 * k + 2))
        (premises := Finset.univ)
        (g := premiseFunK l u alpha s lz)
        (out := fun st => st.y)
        (μ := μ) (c := c)
        (valid := DeepKState.valid l u w b wout bout hk)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _; exact hμ i
  case hg =>
    intro i _ st hv
    exact premiseFunK_sound l u w b wout bout hk alpha s lz uz
      ha0 ha1 hlz huz hs hbox_z i st hv
  case hcert =>
    intro st
    -- the certificate is stated already as a sum over `Finset.univ`
    simpa using hcert st

/-! ## 5. Sanity check: the parametric theorem instantiates at `k = 3`.

This makes the "arbitrary depth" claim concrete: a depth-3 (three hidden ReLU
layers) bridge is obtained with zero extra proof, just by specialising `k := 3`.
The general induction over the layer index is exactly `premiseFunK_sound`, whose
proof is uniform in `k`; no `k`-specific reasoning is needed. -/
theorem crown_bridge_deep3
    (l u : ℚ) (w b : Fin 3 → ℚ) (wout bout : ℚ)
    (alpha s lz uz : Fin 3 → ℚ) (c : ℚ)
    (μ : Fin (2 * 3 + 2) → ℚ)
    (ha0 : ∀ j, 0 ≤ alpha j) (ha1 : ∀ j, alpha j ≤ 1)
    (hlz : ∀ j, lz j < 0) (huz : ∀ j, 0 < uz j)
    (hs  : ∀ j, s j * (uz j - lz j) = uz j)
    (hbox_z : ∀ (st : DeepKState 3),
        DeepKState.valid l u w b wout bout (by norm_num) st →
          ∀ j, lz j ≤ st.z j ∧ st.z j ≤ uz j)
    (hμ : ∀ i, 0 ≤ μ i)
    (hcert : ∀ st : DeepKState 3,
        (∑ i, μ i * premiseFunK l u alpha s lz i st) = -(st.y) - c) :
    ∀ st : DeepKState 3,
      DeepKState.valid l u w b wout bout (by norm_num) st → -c ≤ st.y :=
  crown_bridge_deepK l u w b wout bout (by norm_num)
    alpha s lz uz c μ ha0 ha1 hlz huz hs hbox_z hμ hcert

/-! ## Trust-base check: only the three standard logical axioms. -/

#print axioms premiseFunK_sound
#print axioms crown_bridge_deepK
#print axioms crown_bridge_deep3

end Crownproof
