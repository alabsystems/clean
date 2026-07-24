/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Multi-layer CROWN composition soundness.

`Crownproof.Bridge` proved the end-to-end bridge for ONE unstable-ReLU hidden
layer.  This file shows the composition is genuine: a network with TWO hidden
ReLU layers (x -> z1 -> a1 -> z2 -> a2 -> y) is sound by the SAME general core
`farkas_premise_combination`, instantiated with the larger premise family (box +
the ReLU envelopes of both layers).  The affine layers live in the validity
predicate and the certificate identity, exactly as in the one-layer case, so no
new combination theory is needed — composition is free from the general lemma.

This is the formal content of `farkas_to_interval` for a deep ReLU network.
-/
import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace Crownproof

/-- State of a two-hidden-layer scalar ReLU network. -/
structure Deep2State where
  x  : ℚ
  z1 : ℚ
  a1 : ℚ
  z2 : ℚ
  a2 : ℚ
  y  : ℚ

/-- A genuine execution of the depth-2 network `(w1,b1,w2,b2,w3,b3)` on box
    `[l,u]`: the box holds and every affine + ReLU equation holds. -/
def Deep2State.valid (l u w1 b1 w2 b2 w3 b3 : ℚ) (st : Deep2State) : Prop :=
  l ≤ st.x ∧ st.x ≤ u ∧
  st.z1 = w1 * st.x  + b1 ∧
  st.a1 = relu st.z1 ∧
  st.z2 = w2 * st.a1 + b2 ∧
  st.a2 = relu st.z2 ∧
  st.y  = w3 * st.a2 + b3

/-- The six relaxed-network premises as `lhs ≤ 0` functionals: box (2) plus the
    lower/upper ReLU envelopes of each hidden layer.  `alphai`/`si`/`lzi` are the
    lower-slope / upper-chord-slope / chord lower-anchor of layer `i`. -/
def premiseFun2 (l u alpha1 s1 lz1 alpha2 s2 lz2 : ℚ) :
    Fin 6 → Deep2State → ℚ
  | 0, st => l - st.x                       -- box lower
  | 1, st => st.x - u                       -- box upper
  | 2, st => alpha1 * st.z1 - st.a1         -- layer-1 ReLU lower
  | 3, st => st.a1 - s1 * (st.z1 - lz1)     -- layer-1 ReLU upper
  | 4, st => alpha2 * st.z2 - st.a2         -- layer-2 ReLU lower
  | 5, st => st.a2 - s2 * (st.z2 - lz2)     -- layer-2 ReLU upper

/-- Each depth-2 premise is sound on genuine executions.  Box premises by
    `linarith`; ReLU premises by `relu_lower` / `relu_upper` at the respective
    layer, using the supplied per-layer pre-activation bounds. -/
theorem premiseFun2_sound
    (l u w1 b1 w2 b2 w3 b3 : ℚ)
    (alpha1 s1 lz1 uz1 alpha2 s2 lz2 uz2 : ℚ)
    (ha1₀ : 0 ≤ alpha1) (ha1₁ : alpha1 ≤ 1)
    (hlz1 : lz1 < 0) (huz1 : 0 < uz1) (hs1 : s1 * (uz1 - lz1) = uz1)
    (ha2₀ : 0 ≤ alpha2) (ha2₁ : alpha2 ≤ 1)
    (hlz2 : lz2 < 0) (huz2 : 0 < uz2) (hs2 : s2 * (uz2 - lz2) = uz2)
    (hbox_z1 : ∀ st : Deep2State, Deep2State.valid l u w1 b1 w2 b2 w3 b3 st →
                 lz1 ≤ st.z1 ∧ st.z1 ≤ uz1)
    (hbox_z2 : ∀ st : Deep2State, Deep2State.valid l u w1 b1 w2 b2 w3 b3 st →
                 lz2 ≤ st.z2 ∧ st.z2 ≤ uz2) :
    ∀ i : Fin 6, ∀ st : Deep2State,
      Deep2State.valid l u w1 b1 w2 b2 w3 b3 st →
        premiseFun2 l u alpha1 s1 lz1 alpha2 s2 lz2 i st ≤ 0 := by
  intro i st hv
  obtain ⟨hxl, hxu, hz1, ha1, hz2, ha2, hy⟩ := hv
  fin_cases i
  · simp only [premiseFun2]; linarith
  · simp only [premiseFun2]; linarith
  · -- layer-1 lower envelope, a1 = relu z1
    simp only [premiseFun2]; rw [ha1]
    have := relu_lower alpha1 st.z1 ha1₀ ha1₁
    linarith
  · -- layer-1 upper envelope
    simp only [premiseFun2]; rw [ha1]
    obtain ⟨h1l, h1u⟩ := hbox_z1 st ⟨hxl, hxu, hz1, ha1, hz2, ha2, hy⟩
    have := relu_upper lz1 uz1 s1 st.z1 hlz1 huz1 hs1 h1l h1u
    linarith
  · -- layer-2 lower envelope, a2 = relu z2
    simp only [premiseFun2]; rw [ha2]
    have := relu_lower alpha2 st.z2 ha2₀ ha2₁
    linarith
  · -- layer-2 upper envelope
    simp only [premiseFun2]; rw [ha2]
    obtain ⟨h2l, h2u⟩ := hbox_z2 st ⟨hxl, hxu, hz1, ha1, hz2, ha2, hy⟩
    have := relu_upper lz2 uz2 s2 st.z2 hlz2 huz2 hs2 h2l h2u
    linarith

/--
**Multi-layer CROWN end-to-end bridge** (two hidden ReLU layers).

If six non-negative multipliers combine the six relaxed-network premises so that,
as a function of the state, the combination equals `-(y) - c`, then every genuine
execution of the depth-2 network on the box satisfies `y ≥ -c`.

Proven sorry-free by reduction to the general `farkas_premise_combination` — the
SAME core that proves the one-layer `crown_bridge`.  Composition adds premises,
not new combination theory.
-/
theorem crown_bridge_deep2
    (l u w1 b1 w2 b2 w3 b3 : ℚ)
    (alpha1 s1 lz1 uz1 alpha2 s2 lz2 uz2 c : ℚ)
    (m0 m1 m2 m3 m4 m5 : ℚ)
    (ha1₀ : 0 ≤ alpha1) (ha1₁ : alpha1 ≤ 1)
    (hlz1 : lz1 < 0) (huz1 : 0 < uz1) (hs1 : s1 * (uz1 - lz1) = uz1)
    (ha2₀ : 0 ≤ alpha2) (ha2₁ : alpha2 ≤ 1)
    (hlz2 : lz2 < 0) (huz2 : 0 < uz2) (hs2 : s2 * (uz2 - lz2) = uz2)
    (hbox_z1 : ∀ st : Deep2State, Deep2State.valid l u w1 b1 w2 b2 w3 b3 st →
                 lz1 ≤ st.z1 ∧ st.z1 ≤ uz1)
    (hbox_z2 : ∀ st : Deep2State, Deep2State.valid l u w1 b1 w2 b2 w3 b3 st →
                 lz2 ≤ st.z2 ∧ st.z2 ≤ uz2)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hm3 : 0 ≤ m3) (hm4 : 0 ≤ m4) (hm5 : 0 ≤ m5)
    (hcert : ∀ st : Deep2State,
        m0 * (l - st.x)
      + m1 * (st.x - u)
      + m2 * (alpha1 * st.z1 - st.a1)
      + m3 * (st.a1 - s1 * (st.z1 - lz1))
      + m4 * (alpha2 * st.z2 - st.a2)
      + m5 * (st.a2 - s2 * (st.z2 - lz2))
        = -(st.y) - c) :
    ∀ st : Deep2State, Deep2State.valid l u w1 b1 w2 b2 w3 b3 st → -c ≤ st.y := by
  refine farkas_premise_combination (S := Deep2State) (ι := Fin 6)
        (premises := Finset.univ)
        (g := premiseFun2 l u alpha1 s1 lz1 alpha2 s2 lz2)
        (out := fun st => st.y)
        (μ := ![m0, m1, m2, m3, m4, m5]) (c := c)
        (valid := Deep2State.valid l u w1 b1 w2 b2 w3 b3)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _
    fin_cases i
    · simpa using hm0
    · simpa using hm1
    · simpa using hm2
    · simpa using hm3
    · simpa using hm4
    · simpa using hm5
  case hg =>
    intro i _ st hv
    exact premiseFun2_sound l u w1 b1 w2 b2 w3 b3
      alpha1 s1 lz1 uz1 alpha2 s2 lz2 uz2
      ha1₀ ha1₁ hlz1 huz1 hs1 ha2₀ ha2₁ hlz2 huz2 hs2 hbox_z1 hbox_z2 i st hv
  case hcert =>
    intro st
    have h := hcert st
    simp only [Fin.sum_univ_six, premiseFun2, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
               Matrix.vecHead, Matrix.vecTail, Function.comp]
    linarith [h]

/-! Trust-base check: only the three standard logical axioms. -/

#print axioms premiseFun2_sound
#print axioms crown_bridge_deep2

end Crownproof
