/-
  G1 CLOSURE for a REAL ACAS-Xu net pair.

  The canonical `TwoReluCut.lean` proves the joint cut bound `hB` only as a
  HYPOTHESIS (weight-agnostic) and gives a Lean validity proof of the DERIVED
  bound only for the toy demo weights (z1=x1+x2, z2=x1-x2, B=2,
  `demo_joint_cut_valid`).  This file closes that gap (DEEPCONV_FRONTIER §2.4
  G1) for a GENUINE real-weight instance: the first-hidden-layer neuron pair
  (0,5) of ACAS-Xu net_1_1 over the real prop_1 input box, with exact f32->ℚ
  weights.

  We prove a GENERAL-WEIGHT joint-cut-validity lemma:
  for two ReLUs whose pre-activations are AFFINE in a (here 5-D) box input,
  `relu z1 + relu z2 <= B` where `B` is the corner-maximum of the relu-sum.
  The proof is the convex vertex argument done elementarily: the relu-sum is
  convex, so along each input coordinate it is bounded by the larger of its two
  endpoint values; iterating over the 5 coordinates reduces any box point to a
  corner, and `B` dominates every corner.

  No `sorry`.  `#print axioms` must be [propext, Classical.choice, Quot.sound].
-/
import Crownproof.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic

namespace Crownproof

open scoped BigOperators

/-- One-coordinate convex sup-reduction for a sum of two ReLU-of-affine terms.
For `g t = relu (p*t + c1) + relu (q*t + c2)` and `a ≤ t ≤ b`,
`g t ≤ max (g a) (g b)`.  This is convexity of `g` in the single variable `t`
(sum of two convex piecewise-linear functions), proved elementarily: write
`t = (1-λ)*a + λ*b` with `λ ∈ [0,1]` and bound each `relu` by the convex
combination of its endpoint values using `relu (convex comb) ≤ convex comb of
relu` (subadditivity/convexity of `max 0 ·`). -/
theorem relu2_coord_sup
    (p q c1 c2 a b t : ℚ) (ha : a ≤ t) (hb : t ≤ b) :
    relu (p * t + c1) + relu (q * t + c2)
      ≤ max (relu (p * a + c1) + relu (q * a + c2))
            (relu (p * b + c1) + relu (q * b + c2)) := by
  -- degenerate width: a = b forces t = a = b.
  rcases eq_or_lt_of_le (le_trans ha hb) with hab | hab
  · -- a = b ⇒ t = a, both sides equal.
    have hta : t = a := le_antisymm (hab ▸ hb) ha
    subst hta
    exact le_max_left _ _
  · -- a < b.  λ := (t - a)/(b - a) ∈ [0,1], and t = a + λ*(b-a).
    have hwpos : 0 < b - a := by linarith
    have hwne : b - a ≠ 0 := ne_of_gt hwpos
    let lam : ℚ := (t - a) / (b - a)
    have hlamdef : lam = (t - a) / (b - a) := rfl
    have hlam0 : 0 ≤ lam := by
      rw [hlamdef]; apply div_nonneg _ (le_of_lt hwpos); linarith
    have hlam1 : lam ≤ 1 := by
      rw [hlamdef, div_le_one hwpos]; linarith
    -- t = (1-lam)*a + lam*b
    have hlamw : lam * (b - a) = t - a := by
      rw [hlamdef]; exact div_mul_cancel₀ (t - a) hwne
    have htdecomp : t = (1 - lam) * a + lam * b := by
      have hexp : (1 - lam) * a + lam * b = a + lam * (b - a) := by
        ring
      rw [hexp, hlamw]
      ring
    -- For any affine s*t+c, the value is the convex comb of the endpoint values.
    have affine_comb : ∀ s c : ℚ,
        s * t + c = (1 - lam) * (s * a + c) + lam * (s * b + c) := by
      intro s c; rw [htdecomp]; ring
    -- relu of a convex combination ≤ convex comb of relus (convexity of max 0 ·).
    have relu_convex : ∀ u v : ℚ,
        relu ((1 - lam) * u + lam * v) ≤ (1 - lam) * relu u + lam * relu v := by
      intro u v
      have h1l : 0 ≤ 1 - lam := by linarith
      unfold relu
      -- max 0 (αu+βv) ≤ α(max 0 u)+β(max 0 v) with α=1-lam,β=lam,α,β≥0.
      apply max_le
      · have := mul_nonneg h1l (le_max_left 0 u)
        have := mul_nonneg hlam0 (le_max_left 0 v)
        positivity
      · have hu : u ≤ max 0 u := le_max_right 0 u
        have hv : v ≤ max 0 v := le_max_right 0 v
        have t1 : (1 - lam) * u ≤ (1 - lam) * max 0 u :=
          mul_le_mul_of_nonneg_left hu h1l
        have t2 : lam * v ≤ lam * max 0 v :=
          mul_le_mul_of_nonneg_left hv hlam0
        linarith
    -- Combine: g t ≤ (1-lam)*g a + lam*g b ≤ max (g a) (g b).
    have r1 := relu_convex (p * a + c1) (p * b + c1)
    have r2 := relu_convex (q * a + c2) (q * b + c2)
    rw [affine_comb p c1, affine_comb q c2]
    have hcomb :
        relu ((1 - lam) * (p * a + c1) + lam * (p * b + c1))
          + relu ((1 - lam) * (q * a + c2) + lam * (q * b + c2))
        ≤ (1 - lam) * (relu (p * a + c1) + relu (q * a + c2))
          + lam * (relu (p * b + c1) + relu (q * b + c2)) := by
      have := add_le_add r1 r2; linarith
    refine le_trans hcomb ?_
    -- (1-lam)*A + lam*B ≤ max A B
    have h1l : 0 ≤ 1 - lam := by linarith
    have hA : relu (p * a + c1) + relu (q * a + c2)
        ≤ max (relu (p * a + c1) + relu (q * a + c2))
              (relu (p * b + c1) + relu (q * b + c2)) := le_max_left _ _
    have hB : relu (p * b + c1) + relu (q * b + c2)
        ≤ max (relu (p * a + c1) + relu (q * a + c2))
              (relu (p * b + c1) + relu (q * b + c2)) := le_max_right _ _
    have tA := mul_le_mul_of_nonneg_left hA h1l
    have tB := mul_le_mul_of_nonneg_left hB hlam0
    have hsplit :
        (1 - lam) * max (relu (p * a + c1) + relu (q * a + c2))
                        (relu (p * b + c1) + relu (q * b + c2))
        + lam * max (relu (p * a + c1) + relu (q * a + c2))
                    (relu (p * b + c1) + relu (q * b + c2))
        = max (relu (p * a + c1) + relu (q * a + c2))
              (relu (p * b + c1) + relu (q * b + c2)) := by ring
    linarith [tA, tB, hsplit.ge]


/-! ## General 5-D box corner-domination (the G1 general-weight lemma).

For `z1 = Σ a_k x_k + r1`, `z2 = Σ d_k x_k + r2` affine over a 5-D box, the
relu-sum is convex, so its value at any box point is `≤` its maximum over the
32 corners.  We peel one coordinate at a time with `relu2_coord_sup`.  The 32
corner values are supplied via `hcorner`; the conclusion is the joint cut bound
for an arbitrary box point.  This is exactly the `hB` hypothesis of
`cutPremise_sound` / `twoReluCut_bridge`, discharged for ARBITRARY rational
weights — closing DEEPCONV_FRONTIER §2.4 G1. -/
theorem relu2_box5_le
    (a0 a1 a2 a3 a4 r1 d0 d1 d2 d3 d4 r2 : ℚ)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℚ)
    (B : ℚ)
    (hcorner : ∀ e0 ∈ ({l0, u0} : Set ℚ), ∀ e1 ∈ ({l1, u1} : Set ℚ),
               ∀ e2 ∈ ({l2, u2} : Set ℚ), ∀ e3 ∈ ({l3, u3} : Set ℚ),
               ∀ e4 ∈ ({l4, u4} : Set ℚ),
        relu (a0*e0+a1*e1+a2*e2+a3*e3+a4*e4+r1)
      + relu (d0*e0+d1*e1+d2*e2+d3*e3+d4*e4+r2) ≤ B)
    (x0 x1 x2 x3 x4 : ℚ)
    (hx0 : l0 ≤ x0) (hx0' : x0 ≤ u0) (hx1 : l1 ≤ x1) (hx1' : x1 ≤ u1)
    (hx2 : l2 ≤ x2) (hx2' : x2 ≤ u2) (hx3 : l3 ≤ x3) (hx3' : x3 ≤ u3)
    (hx4 : l4 ≤ x4) (hx4' : x4 ≤ u4) :
    relu (a0*x0+a1*x1+a2*x2+a3*x3+a4*x4+r1)
  + relu (d0*x0+d1*x1+d2*x2+d3*x3+d4*x4+r2) ≤ B := by
  have peel : ∀ (ak dk cA cD lk uk t Φ : ℚ), lk ≤ t → t ≤ uk →
      (relu (ak*lk + cA) + relu (dk*lk + cD) ≤ Φ) →
      (relu (ak*uk + cA) + relu (dk*uk + cD) ≤ Φ) →
      relu (ak*t + cA) + relu (dk*t + cD) ≤ Φ := by
    intro ak dk cA dD lk uk t Φ hlt htu hlo hhi
    exact le_trans (relu2_coord_sup ak dk cA dD lk uk t hlt htu) (max_le hlo hhi)

  rw [show a0*x0+a1*x1+a2*x2+a3*x3+a4*x4+r1 = a0*x0 + (a1*x1+a2*x2+a3*x3+a4*x4+r1) from by ring, show d0*x0+d1*x1+d2*x2+d3*x3+d4*x4+r2 = d0*x0 + (d1*x1+d2*x2+d3*x3+d4*x4+r2) from by ring]
  refine peel a0 d0 (a1*x1+a2*x2+a3*x3+a4*x4+r1) (d1*x1+d2*x2+d3*x3+d4*x4+r2) l0 u0 x0 B hx0 hx0' ?_ ?_
  · 
    rw [show a0*l0 + (a1*x1+a2*x2+a3*x3+a4*x4+r1) = a1*x1 + (a0*l0+a2*x2+a3*x3+a4*x4+r1) from by ring, show d0*l0 + (d1*x1+d2*x2+d3*x3+d4*x4+r2) = d1*x1 + (d0*l0+d2*x2+d3*x3+d4*x4+r2) from by ring]
    refine peel a1 d1 (a0*l0+a2*x2+a3*x3+a4*x4+r1) (d0*l0+d2*x2+d3*x3+d4*x4+r2) l1 u1 x1 B hx1 hx1' ?_ ?_
    · 
      rw [show a1*l1 + (a0*l0+a2*x2+a3*x3+a4*x4+r1) = a2*x2 + (a0*l0+a1*l1+a3*x3+a4*x4+r1) from by ring, show d1*l1 + (d0*l0+d2*x2+d3*x3+d4*x4+r2) = d2*x2 + (d0*l0+d1*l1+d3*x3+d4*x4+r2) from by ring]
      refine peel a2 d2 (a0*l0+a1*l1+a3*x3+a4*x4+r1) (d0*l0+d1*l1+d3*x3+d4*x4+r2) l2 u2 x2 B hx2 hx2' ?_ ?_
      · 
        rw [show a2*l2 + (a0*l0+a1*l1+a3*x3+a4*x4+r1) = a3*x3 + (a0*l0+a1*l1+a2*l2+a4*x4+r1) from by ring, show d2*l2 + (d0*l0+d1*l1+d3*x3+d4*x4+r2) = d3*x3 + (d0*l0+d1*l1+d2*l2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*l0+a1*l1+a2*l2+a4*x4+r1) (d0*l0+d1*l1+d2*l2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*l0+a1*l1+a2*l2+a4*x4+r1) = a4*x4 + (a0*l0+a1*l1+a2*l2+a3*l3+r1) from by ring, show d3*l3 + (d0*l0+d1*l1+d2*l2+d4*x4+r2) = d4*x4 + (d0*l0+d1*l1+d2*l2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*l1+a2*l2+a3*l3+r1) (d0*l0+d1*l1+d2*l2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*l1+a2*l2+a3*l3+r1)) + relu (d4*l4 + (d0*l0+d1*l1+d2*l2+d3*l3+r2))
                = relu (a0*l0+a1*l1+a2*l2+a3*l3+a4*l4+r1) + relu (d0*l0+d1*l1+d2*l2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*l1+a2*l2+a3*l3+r1)) + relu (d4*u4 + (d0*l0+d1*l1+d2*l2+d3*l3+r2))
                = relu (a0*l0+a1*l1+a2*l2+a3*l3+a4*u4+r1) + relu (d0*l0+d1*l1+d2*l2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*l0+a1*l1+a2*l2+a4*x4+r1) = a4*x4 + (a0*l0+a1*l1+a2*l2+a3*u3+r1) from by ring, show d3*u3 + (d0*l0+d1*l1+d2*l2+d4*x4+r2) = d4*x4 + (d0*l0+d1*l1+d2*l2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*l1+a2*l2+a3*u3+r1) (d0*l0+d1*l1+d2*l2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*l1+a2*l2+a3*u3+r1)) + relu (d4*l4 + (d0*l0+d1*l1+d2*l2+d3*u3+r2))
                = relu (a0*l0+a1*l1+a2*l2+a3*u3+a4*l4+r1) + relu (d0*l0+d1*l1+d2*l2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*l1+a2*l2+a3*u3+r1)) + relu (d4*u4 + (d0*l0+d1*l1+d2*l2+d3*u3+r2))
                = relu (a0*l0+a1*l1+a2*l2+a3*u3+a4*u4+r1) + relu (d0*l0+d1*l1+d2*l2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
      · 
        rw [show a2*u2 + (a0*l0+a1*l1+a3*x3+a4*x4+r1) = a3*x3 + (a0*l0+a1*l1+a2*u2+a4*x4+r1) from by ring, show d2*u2 + (d0*l0+d1*l1+d3*x3+d4*x4+r2) = d3*x3 + (d0*l0+d1*l1+d2*u2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*l0+a1*l1+a2*u2+a4*x4+r1) (d0*l0+d1*l1+d2*u2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*l0+a1*l1+a2*u2+a4*x4+r1) = a4*x4 + (a0*l0+a1*l1+a2*u2+a3*l3+r1) from by ring, show d3*l3 + (d0*l0+d1*l1+d2*u2+d4*x4+r2) = d4*x4 + (d0*l0+d1*l1+d2*u2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*l1+a2*u2+a3*l3+r1) (d0*l0+d1*l1+d2*u2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*l1+a2*u2+a3*l3+r1)) + relu (d4*l4 + (d0*l0+d1*l1+d2*u2+d3*l3+r2))
                = relu (a0*l0+a1*l1+a2*u2+a3*l3+a4*l4+r1) + relu (d0*l0+d1*l1+d2*u2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*l1+a2*u2+a3*l3+r1)) + relu (d4*u4 + (d0*l0+d1*l1+d2*u2+d3*l3+r2))
                = relu (a0*l0+a1*l1+a2*u2+a3*l3+a4*u4+r1) + relu (d0*l0+d1*l1+d2*u2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*l0+a1*l1+a2*u2+a4*x4+r1) = a4*x4 + (a0*l0+a1*l1+a2*u2+a3*u3+r1) from by ring, show d3*u3 + (d0*l0+d1*l1+d2*u2+d4*x4+r2) = d4*x4 + (d0*l0+d1*l1+d2*u2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*l1+a2*u2+a3*u3+r1) (d0*l0+d1*l1+d2*u2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*l1+a2*u2+a3*u3+r1)) + relu (d4*l4 + (d0*l0+d1*l1+d2*u2+d3*u3+r2))
                = relu (a0*l0+a1*l1+a2*u2+a3*u3+a4*l4+r1) + relu (d0*l0+d1*l1+d2*u2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*l1+a2*u2+a3*u3+r1)) + relu (d4*u4 + (d0*l0+d1*l1+d2*u2+d3*u3+r2))
                = relu (a0*l0+a1*l1+a2*u2+a3*u3+a4*u4+r1) + relu (d0*l0+d1*l1+d2*u2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
    · 
      rw [show a1*u1 + (a0*l0+a2*x2+a3*x3+a4*x4+r1) = a2*x2 + (a0*l0+a1*u1+a3*x3+a4*x4+r1) from by ring, show d1*u1 + (d0*l0+d2*x2+d3*x3+d4*x4+r2) = d2*x2 + (d0*l0+d1*u1+d3*x3+d4*x4+r2) from by ring]
      refine peel a2 d2 (a0*l0+a1*u1+a3*x3+a4*x4+r1) (d0*l0+d1*u1+d3*x3+d4*x4+r2) l2 u2 x2 B hx2 hx2' ?_ ?_
      · 
        rw [show a2*l2 + (a0*l0+a1*u1+a3*x3+a4*x4+r1) = a3*x3 + (a0*l0+a1*u1+a2*l2+a4*x4+r1) from by ring, show d2*l2 + (d0*l0+d1*u1+d3*x3+d4*x4+r2) = d3*x3 + (d0*l0+d1*u1+d2*l2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*l0+a1*u1+a2*l2+a4*x4+r1) (d0*l0+d1*u1+d2*l2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*l0+a1*u1+a2*l2+a4*x4+r1) = a4*x4 + (a0*l0+a1*u1+a2*l2+a3*l3+r1) from by ring, show d3*l3 + (d0*l0+d1*u1+d2*l2+d4*x4+r2) = d4*x4 + (d0*l0+d1*u1+d2*l2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*u1+a2*l2+a3*l3+r1) (d0*l0+d1*u1+d2*l2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*u1+a2*l2+a3*l3+r1)) + relu (d4*l4 + (d0*l0+d1*u1+d2*l2+d3*l3+r2))
                = relu (a0*l0+a1*u1+a2*l2+a3*l3+a4*l4+r1) + relu (d0*l0+d1*u1+d2*l2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*u1+a2*l2+a3*l3+r1)) + relu (d4*u4 + (d0*l0+d1*u1+d2*l2+d3*l3+r2))
                = relu (a0*l0+a1*u1+a2*l2+a3*l3+a4*u4+r1) + relu (d0*l0+d1*u1+d2*l2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*l0+a1*u1+a2*l2+a4*x4+r1) = a4*x4 + (a0*l0+a1*u1+a2*l2+a3*u3+r1) from by ring, show d3*u3 + (d0*l0+d1*u1+d2*l2+d4*x4+r2) = d4*x4 + (d0*l0+d1*u1+d2*l2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*u1+a2*l2+a3*u3+r1) (d0*l0+d1*u1+d2*l2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*u1+a2*l2+a3*u3+r1)) + relu (d4*l4 + (d0*l0+d1*u1+d2*l2+d3*u3+r2))
                = relu (a0*l0+a1*u1+a2*l2+a3*u3+a4*l4+r1) + relu (d0*l0+d1*u1+d2*l2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*u1+a2*l2+a3*u3+r1)) + relu (d4*u4 + (d0*l0+d1*u1+d2*l2+d3*u3+r2))
                = relu (a0*l0+a1*u1+a2*l2+a3*u3+a4*u4+r1) + relu (d0*l0+d1*u1+d2*l2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
      · 
        rw [show a2*u2 + (a0*l0+a1*u1+a3*x3+a4*x4+r1) = a3*x3 + (a0*l0+a1*u1+a2*u2+a4*x4+r1) from by ring, show d2*u2 + (d0*l0+d1*u1+d3*x3+d4*x4+r2) = d3*x3 + (d0*l0+d1*u1+d2*u2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*l0+a1*u1+a2*u2+a4*x4+r1) (d0*l0+d1*u1+d2*u2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*l0+a1*u1+a2*u2+a4*x4+r1) = a4*x4 + (a0*l0+a1*u1+a2*u2+a3*l3+r1) from by ring, show d3*l3 + (d0*l0+d1*u1+d2*u2+d4*x4+r2) = d4*x4 + (d0*l0+d1*u1+d2*u2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*u1+a2*u2+a3*l3+r1) (d0*l0+d1*u1+d2*u2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*u1+a2*u2+a3*l3+r1)) + relu (d4*l4 + (d0*l0+d1*u1+d2*u2+d3*l3+r2))
                = relu (a0*l0+a1*u1+a2*u2+a3*l3+a4*l4+r1) + relu (d0*l0+d1*u1+d2*u2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*u1+a2*u2+a3*l3+r1)) + relu (d4*u4 + (d0*l0+d1*u1+d2*u2+d3*l3+r2))
                = relu (a0*l0+a1*u1+a2*u2+a3*l3+a4*u4+r1) + relu (d0*l0+d1*u1+d2*u2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*l0+a1*u1+a2*u2+a4*x4+r1) = a4*x4 + (a0*l0+a1*u1+a2*u2+a3*u3+r1) from by ring, show d3*u3 + (d0*l0+d1*u1+d2*u2+d4*x4+r2) = d4*x4 + (d0*l0+d1*u1+d2*u2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*l0+a1*u1+a2*u2+a3*u3+r1) (d0*l0+d1*u1+d2*u2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*l0+a1*u1+a2*u2+a3*u3+r1)) + relu (d4*l4 + (d0*l0+d1*u1+d2*u2+d3*u3+r2))
                = relu (a0*l0+a1*u1+a2*u2+a3*u3+a4*l4+r1) + relu (d0*l0+d1*u1+d2*u2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner l0 (show l0 ∈ ({l0, u0} : Set ℚ) by left; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*l0+a1*u1+a2*u2+a3*u3+r1)) + relu (d4*u4 + (d0*l0+d1*u1+d2*u2+d3*u3+r2))
                = relu (a0*l0+a1*u1+a2*u2+a3*u3+a4*u4+r1) + relu (d0*l0+d1*u1+d2*u2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
  · 
    rw [show a0*u0 + (a1*x1+a2*x2+a3*x3+a4*x4+r1) = a1*x1 + (a0*u0+a2*x2+a3*x3+a4*x4+r1) from by ring, show d0*u0 + (d1*x1+d2*x2+d3*x3+d4*x4+r2) = d1*x1 + (d0*u0+d2*x2+d3*x3+d4*x4+r2) from by ring]
    refine peel a1 d1 (a0*u0+a2*x2+a3*x3+a4*x4+r1) (d0*u0+d2*x2+d3*x3+d4*x4+r2) l1 u1 x1 B hx1 hx1' ?_ ?_
    · 
      rw [show a1*l1 + (a0*u0+a2*x2+a3*x3+a4*x4+r1) = a2*x2 + (a0*u0+a1*l1+a3*x3+a4*x4+r1) from by ring, show d1*l1 + (d0*u0+d2*x2+d3*x3+d4*x4+r2) = d2*x2 + (d0*u0+d1*l1+d3*x3+d4*x4+r2) from by ring]
      refine peel a2 d2 (a0*u0+a1*l1+a3*x3+a4*x4+r1) (d0*u0+d1*l1+d3*x3+d4*x4+r2) l2 u2 x2 B hx2 hx2' ?_ ?_
      · 
        rw [show a2*l2 + (a0*u0+a1*l1+a3*x3+a4*x4+r1) = a3*x3 + (a0*u0+a1*l1+a2*l2+a4*x4+r1) from by ring, show d2*l2 + (d0*u0+d1*l1+d3*x3+d4*x4+r2) = d3*x3 + (d0*u0+d1*l1+d2*l2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*u0+a1*l1+a2*l2+a4*x4+r1) (d0*u0+d1*l1+d2*l2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*u0+a1*l1+a2*l2+a4*x4+r1) = a4*x4 + (a0*u0+a1*l1+a2*l2+a3*l3+r1) from by ring, show d3*l3 + (d0*u0+d1*l1+d2*l2+d4*x4+r2) = d4*x4 + (d0*u0+d1*l1+d2*l2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*l1+a2*l2+a3*l3+r1) (d0*u0+d1*l1+d2*l2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*l1+a2*l2+a3*l3+r1)) + relu (d4*l4 + (d0*u0+d1*l1+d2*l2+d3*l3+r2))
                = relu (a0*u0+a1*l1+a2*l2+a3*l3+a4*l4+r1) + relu (d0*u0+d1*l1+d2*l2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*l1+a2*l2+a3*l3+r1)) + relu (d4*u4 + (d0*u0+d1*l1+d2*l2+d3*l3+r2))
                = relu (a0*u0+a1*l1+a2*l2+a3*l3+a4*u4+r1) + relu (d0*u0+d1*l1+d2*l2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*u0+a1*l1+a2*l2+a4*x4+r1) = a4*x4 + (a0*u0+a1*l1+a2*l2+a3*u3+r1) from by ring, show d3*u3 + (d0*u0+d1*l1+d2*l2+d4*x4+r2) = d4*x4 + (d0*u0+d1*l1+d2*l2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*l1+a2*l2+a3*u3+r1) (d0*u0+d1*l1+d2*l2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*l1+a2*l2+a3*u3+r1)) + relu (d4*l4 + (d0*u0+d1*l1+d2*l2+d3*u3+r2))
                = relu (a0*u0+a1*l1+a2*l2+a3*u3+a4*l4+r1) + relu (d0*u0+d1*l1+d2*l2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*l1+a2*l2+a3*u3+r1)) + relu (d4*u4 + (d0*u0+d1*l1+d2*l2+d3*u3+r2))
                = relu (a0*u0+a1*l1+a2*l2+a3*u3+a4*u4+r1) + relu (d0*u0+d1*l1+d2*l2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
      · 
        rw [show a2*u2 + (a0*u0+a1*l1+a3*x3+a4*x4+r1) = a3*x3 + (a0*u0+a1*l1+a2*u2+a4*x4+r1) from by ring, show d2*u2 + (d0*u0+d1*l1+d3*x3+d4*x4+r2) = d3*x3 + (d0*u0+d1*l1+d2*u2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*u0+a1*l1+a2*u2+a4*x4+r1) (d0*u0+d1*l1+d2*u2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*u0+a1*l1+a2*u2+a4*x4+r1) = a4*x4 + (a0*u0+a1*l1+a2*u2+a3*l3+r1) from by ring, show d3*l3 + (d0*u0+d1*l1+d2*u2+d4*x4+r2) = d4*x4 + (d0*u0+d1*l1+d2*u2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*l1+a2*u2+a3*l3+r1) (d0*u0+d1*l1+d2*u2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*l1+a2*u2+a3*l3+r1)) + relu (d4*l4 + (d0*u0+d1*l1+d2*u2+d3*l3+r2))
                = relu (a0*u0+a1*l1+a2*u2+a3*l3+a4*l4+r1) + relu (d0*u0+d1*l1+d2*u2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*l1+a2*u2+a3*l3+r1)) + relu (d4*u4 + (d0*u0+d1*l1+d2*u2+d3*l3+r2))
                = relu (a0*u0+a1*l1+a2*u2+a3*l3+a4*u4+r1) + relu (d0*u0+d1*l1+d2*u2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*u0+a1*l1+a2*u2+a4*x4+r1) = a4*x4 + (a0*u0+a1*l1+a2*u2+a3*u3+r1) from by ring, show d3*u3 + (d0*u0+d1*l1+d2*u2+d4*x4+r2) = d4*x4 + (d0*u0+d1*l1+d2*u2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*l1+a2*u2+a3*u3+r1) (d0*u0+d1*l1+d2*u2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*l1+a2*u2+a3*u3+r1)) + relu (d4*l4 + (d0*u0+d1*l1+d2*u2+d3*u3+r2))
                = relu (a0*u0+a1*l1+a2*u2+a3*u3+a4*l4+r1) + relu (d0*u0+d1*l1+d2*u2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) l1 (show l1 ∈ ({l1, u1} : Set ℚ) by left; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*l1+a2*u2+a3*u3+r1)) + relu (d4*u4 + (d0*u0+d1*l1+d2*u2+d3*u3+r2))
                = relu (a0*u0+a1*l1+a2*u2+a3*u3+a4*u4+r1) + relu (d0*u0+d1*l1+d2*u2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
    · 
      rw [show a1*u1 + (a0*u0+a2*x2+a3*x3+a4*x4+r1) = a2*x2 + (a0*u0+a1*u1+a3*x3+a4*x4+r1) from by ring, show d1*u1 + (d0*u0+d2*x2+d3*x3+d4*x4+r2) = d2*x2 + (d0*u0+d1*u1+d3*x3+d4*x4+r2) from by ring]
      refine peel a2 d2 (a0*u0+a1*u1+a3*x3+a4*x4+r1) (d0*u0+d1*u1+d3*x3+d4*x4+r2) l2 u2 x2 B hx2 hx2' ?_ ?_
      · 
        rw [show a2*l2 + (a0*u0+a1*u1+a3*x3+a4*x4+r1) = a3*x3 + (a0*u0+a1*u1+a2*l2+a4*x4+r1) from by ring, show d2*l2 + (d0*u0+d1*u1+d3*x3+d4*x4+r2) = d3*x3 + (d0*u0+d1*u1+d2*l2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*u0+a1*u1+a2*l2+a4*x4+r1) (d0*u0+d1*u1+d2*l2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*u0+a1*u1+a2*l2+a4*x4+r1) = a4*x4 + (a0*u0+a1*u1+a2*l2+a3*l3+r1) from by ring, show d3*l3 + (d0*u0+d1*u1+d2*l2+d4*x4+r2) = d4*x4 + (d0*u0+d1*u1+d2*l2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*u1+a2*l2+a3*l3+r1) (d0*u0+d1*u1+d2*l2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*u1+a2*l2+a3*l3+r1)) + relu (d4*l4 + (d0*u0+d1*u1+d2*l2+d3*l3+r2))
                = relu (a0*u0+a1*u1+a2*l2+a3*l3+a4*l4+r1) + relu (d0*u0+d1*u1+d2*l2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*u1+a2*l2+a3*l3+r1)) + relu (d4*u4 + (d0*u0+d1*u1+d2*l2+d3*l3+r2))
                = relu (a0*u0+a1*u1+a2*l2+a3*l3+a4*u4+r1) + relu (d0*u0+d1*u1+d2*l2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*u0+a1*u1+a2*l2+a4*x4+r1) = a4*x4 + (a0*u0+a1*u1+a2*l2+a3*u3+r1) from by ring, show d3*u3 + (d0*u0+d1*u1+d2*l2+d4*x4+r2) = d4*x4 + (d0*u0+d1*u1+d2*l2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*u1+a2*l2+a3*u3+r1) (d0*u0+d1*u1+d2*l2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*u1+a2*l2+a3*u3+r1)) + relu (d4*l4 + (d0*u0+d1*u1+d2*l2+d3*u3+r2))
                = relu (a0*u0+a1*u1+a2*l2+a3*u3+a4*l4+r1) + relu (d0*u0+d1*u1+d2*l2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) l2 (show l2 ∈ ({l2, u2} : Set ℚ) by left; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*u1+a2*l2+a3*u3+r1)) + relu (d4*u4 + (d0*u0+d1*u1+d2*l2+d3*u3+r2))
                = relu (a0*u0+a1*u1+a2*l2+a3*u3+a4*u4+r1) + relu (d0*u0+d1*u1+d2*l2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
      · 
        rw [show a2*u2 + (a0*u0+a1*u1+a3*x3+a4*x4+r1) = a3*x3 + (a0*u0+a1*u1+a2*u2+a4*x4+r1) from by ring, show d2*u2 + (d0*u0+d1*u1+d3*x3+d4*x4+r2) = d3*x3 + (d0*u0+d1*u1+d2*u2+d4*x4+r2) from by ring]
        refine peel a3 d3 (a0*u0+a1*u1+a2*u2+a4*x4+r1) (d0*u0+d1*u1+d2*u2+d4*x4+r2) l3 u3 x3 B hx3 hx3' ?_ ?_
        · 
          rw [show a3*l3 + (a0*u0+a1*u1+a2*u2+a4*x4+r1) = a4*x4 + (a0*u0+a1*u1+a2*u2+a3*l3+r1) from by ring, show d3*l3 + (d0*u0+d1*u1+d2*u2+d4*x4+r2) = d4*x4 + (d0*u0+d1*u1+d2*u2+d3*l3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*u1+a2*u2+a3*l3+r1) (d0*u0+d1*u1+d2*u2+d3*l3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*u1+a2*u2+a3*l3+r1)) + relu (d4*l4 + (d0*u0+d1*u1+d2*u2+d3*l3+r2))
                = relu (a0*u0+a1*u1+a2*u2+a3*l3+a4*l4+r1) + relu (d0*u0+d1*u1+d2*u2+d3*l3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) l3 (show l3 ∈ ({l3, u3} : Set ℚ) by left; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*u1+a2*u2+a3*l3+r1)) + relu (d4*u4 + (d0*u0+d1*u1+d2*u2+d3*l3+r2))
                = relu (a0*u0+a1*u1+a2*u2+a3*l3+a4*u4+r1) + relu (d0*u0+d1*u1+d2*u2+d3*l3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc
        · 
          rw [show a3*u3 + (a0*u0+a1*u1+a2*u2+a4*x4+r1) = a4*x4 + (a0*u0+a1*u1+a2*u2+a3*u3+r1) from by ring, show d3*u3 + (d0*u0+d1*u1+d2*u2+d4*x4+r2) = d4*x4 + (d0*u0+d1*u1+d2*u2+d3*u3+r2) from by ring]
          refine peel a4 d4 (a0*u0+a1*u1+a2*u2+a3*u3+r1) (d0*u0+d1*u1+d2*u2+d3*u3+r2) l4 u4 x4 B hx4 hx4' ?_ ?_
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) l4 (show l4 ∈ ({l4, u4} : Set ℚ) by left; rfl)
            calc relu (a4*l4 + (a0*u0+a1*u1+a2*u2+a3*u3+r1)) + relu (d4*l4 + (d0*u0+d1*u1+d2*u2+d3*u3+r2))
                = relu (a0*u0+a1*u1+a2*u2+a3*u3+a4*l4+r1) + relu (d0*u0+d1*u1+d2*u2+d3*u3+d4*l4+r2) := by ring_nf
              _ ≤ B := hc
          · 
            have hc := hcorner u0 (show u0 ∈ ({l0, u0} : Set ℚ) by right; rfl) u1 (show u1 ∈ ({l1, u1} : Set ℚ) by right; rfl) u2 (show u2 ∈ ({l2, u2} : Set ℚ) by right; rfl) u3 (show u3 ∈ ({l3, u3} : Set ℚ) by right; rfl) u4 (show u4 ∈ ({l4, u4} : Set ℚ) by right; rfl)
            calc relu (a4*u4 + (a0*u0+a1*u1+a2*u2+a3*u3+r1)) + relu (d4*u4 + (d0*u0+d1*u1+d2*u2+d3*u3+r2))
                = relu (a0*u0+a1*u1+a2*u2+a3*u3+a4*u4+r1) + relu (d0*u0+d1*u1+d2*u2+d3*u3+d4*u4+r2) := by ring_nf
              _ ≤ B := hc

/-! ## REAL ACAS-Xu net_1_1 instance: first-layer neuron pair (0,5).
Exact f32->ℚ weights; prop_1 input box.  `Bcut` is the corner-max of the
relu-sum.  `acas_0_5_joint_cut` certifies the joint cut bound holds for
EVERY point of the real input box — the general-weight `hB`, on real weights. -/
def w0_0 : ℚ := ((14497179 : ℚ)/268435456)
def w0_1 : ℚ := ((-684437 : ℚ)/262144)
def w0_2 : ℚ := ((-12081407 : ℚ)/67108864)
def w0_3 : ℚ := ((4063341 : ℚ)/16777216)
def w0_4 : ℚ := ((9489663 : ℚ)/67108864)
def b0 : ℚ := ((15275991 : ℚ)/67108864)
def w5_0 : ℚ := ((-9178291 : ℚ)/268435456)
def w5_1 : ℚ := ((12546841 : ℚ)/8388608)
def w5_2 : ℚ := ((-3216423 : ℚ)/2097152)
def w5_3 : ℚ := ((10873059 : ℚ)/268435456)
def w5_4 : ℚ := ((5514671 : ℚ)/33554432)
def b5 : ℚ := ((-9875925 : ℚ)/16777216)
def L0 : ℚ := ((3 : ℚ)/5)
def U0 : ℚ := ((679857769 : ℚ)/1000000000)
def L1 : ℚ := ((-1 : ℚ)/2)
def U1 : ℚ := ((1 : ℚ)/2)
def L2 : ℚ := ((-1 : ℚ)/2)
def U2 : ℚ := ((1 : ℚ)/2)
def L3 : ℚ := ((9 : ℚ)/20)
def U3 : ℚ := ((1 : ℚ)/2)
def L4 : ℚ := ((-1 : ℚ)/2)
def U4 : ℚ := ((-9 : ℚ)/20)
def Bcut : ℚ := ((460979876371733651 : ℚ)/268435456000000000)

theorem acas_0_5_joint_cut
    (x0 x1 x2 x3 x4 : ℚ)
    (h0 : L0 ≤ x0) (h0' : x0 ≤ U0) (h1 : L1 ≤ x1) (h1' : x1 ≤ U1)
    (h2 : L2 ≤ x2) (h2' : x2 ≤ U2) (h3 : L3 ≤ x3) (h3' : x3 ≤ U3)
    (h4 : L4 ≤ x4) (h4' : x4 ≤ U4) :
    relu (w0_0*x0+w0_1*x1+w0_2*x2+w0_3*x3+w0_4*x4+b0)
  + relu (w5_0*x0+w5_1*x1+w5_2*x2+w5_3*x3+w5_4*x4+b5) ≤ Bcut := by
  refine relu2_box5_le
    w0_0 w0_1 w0_2 w0_3 w0_4 b0 w5_0 w5_1 w5_2 w5_3 w5_4 b5
    L0 U0 L1 U1 L2 U2 L3 U3 L4 U4 Bcut
    ?hc x0 x1 x2 x3 x4 h0 h0' h1 h1' h2 h2' h3 h3' h4 h4'
  -- the 32-corner bound (general-weight hB, discharged on the real weights)
  intro e0 m0 e1 m1 e2 m2 e3 m3 e4 m4
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m0 m1 m2 m3 m4
  rcases m0 with h|h <;> subst h <;>
    rcases m1 with h|h <;> subst h <;>
    rcases m2 with h|h <;> subst h <;>
    rcases m3 with h|h <;> subst h <;>
    rcases m4 with h|h <;> subst h <;>
    simp only [relu, w0_0, w0_1, w0_2, w0_3, w0_4, b0, w5_0, w5_1, w5_2, w5_3, w5_4, b5,
      L0, U0, L1, U1, L2, U2, L3, U3, L4, U4, Bcut] <;> norm_num

#print axioms relu2_coord_sup
#print axioms relu2_box5_le
#print axioms acas_0_5_joint_cut

end Crownproof
