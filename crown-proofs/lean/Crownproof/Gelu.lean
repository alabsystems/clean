/-
  CROWN linear envelopes for the SMOOTH activations of real transformers,
  formalized in Lean 4 over the reals with mathlib.  This file broadens
  activation coverage beyond ReLU (Basic) and the LayerNorm reciprocal
  square-root (Rsqrt) to:

    * `exp`     — the exponential, building block of every smooth activation;
    * `sigmoid` — the logistic `s(x) = 1/(1 + exp (-x))`;
    * `tanh`    — the hyperbolic tangent, `tanh x = 2·sigmoid (2x) - 1`;
    * the tanh-approximation `gelu`.

  ---------------------------------------------------------------------------
  WHAT CROWN NEEDS.  For a unary nonlinearity `f` and a box `[lo, hi]`, CROWN
  emits two AFFINE functions with `L(x) ≤ f(x) ≤ U(x)` on the whole box.
  Soundness of that relaxation is exactly the pair of envelope inequalities.

  Two universally-valid sources of such bounds for a CONVEX `f`:

    * SECANT (UPPER): a convex function lies on/below the chord through its two
      endpoints.  This is `ConvexOn.2`, the definition of convexity, applied to
      the convex-combination point `x = a·lo + b·hi`.
    * TANGENT (LOWER): a convex function lies on/above each of its tangents;
      anchored at the left endpoint `lo` this gives a lower line on `[lo, hi]`.
      This is mathlib's `ConvexOn.le_slope_of_hasDerivAt`.

  For a CONCAVE `f` the two roles swap (chord below, tangent above), which we
  obtain by dualizing.  `sigmoid` and `tanh` are S-shaped — convex on `x ≤ 0`,
  concave on `x ≥ 0` — so we deliver their envelopes on each sign-definite
  half, the genuinely sound regions for the corresponding chord/tangent.

  ---------------------------------------------------------------------------
  WHAT IS PROVEN (all `sorry`-free; trust base = the 3 standard axioms):

    exp_lower / exp_upper            : tangent / secant envelopes for `exp`.
    convexOn_sigmoid_Iic             : `sigmoid` convex on `(-∞, 0]`.
    concaveOn_sigmoid_Ici            : `sigmoid` concave on `[0, ∞)`.
    sigmoid_lower_convex / _upper_convex : envelopes on a box `[lo,hi] ⊆ Iic 0`.
    sigmoid_upper_concave / _lower_concave : envelopes on `[lo,hi] ⊆ Ici 0`.
    tanh_eq_sigmoid                  : `tanh x = 2·sigmoid (2x) - 1`.
    tanh_{upper,lower}_convex        : tanh envelopes on `[lo,hi] ⊆ Iic 0`.
    tanh_{lower,upper}_concave       : tanh envelopes on `[lo,hi] ⊆ Ici 0`.
                                       (reduced to the sigmoid envelopes at the
                                        doubled points via `tanh_eq_sigmoid`.)
    geluTanh, gelu_envelope_*        : sound (loose) sign-split GELU bounds.

  The S-shape convexity facts are proven from the monotonicity of the first
  derivative (`MonotoneOn.convexOn_of_deriv`), where `deriv sigmoid = s·(1-s)`
  is already a mathlib lemma; the rest is ordered-field reasoning.
-/

import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace Crownproof

open Real Set

/-! ## 0. Generic envelope extractors from a one-sided convexity hypothesis.

These turn an abstract `ConvexOn`/`ConcaveOn` fact plus a `HasDerivAt` into the
two affine CROWN envelopes.  They are stated generically and reused for
`sigmoid`, `tanh`, and (via duality) the concave halves. -/

/-- **Generic tangent (lower) envelope.**  If `f` is convex on `S`, `lo ∈ S`,
    `f` has derivative `d` at `lo`, then on `S` (to the right of `lo`)

        f lo + d · (x - lo) ≤ f x.

    On a CROWN box `lo` is the minimum, so `lo ≤ x` always holds. -/
theorem conv_tangent {S : Set ℝ} {f : ℝ → ℝ} {lo d : ℝ}
    (hfc : ConvexOn ℝ S f) (hlo : lo ∈ S) (hd : HasDerivAt f d lo)
    {x : ℝ} (hx : x ∈ S) (hle : lo ≤ x) :
    f lo + d * (x - lo) ≤ f x := by
  rcases eq_or_lt_of_le hle with h | h
  · subst h; simp
  · have hs := hfc.le_slope_of_hasDerivAt hlo hx h hd
    rw [slope_def_field] at hs
    have hpos : 0 < x - lo := by linarith
    rw [le_div_iff₀ hpos] at hs
    nlinarith [hs]

/-- **Generic secant (upper) envelope.**  If `f` is convex on `S` and
    `lo, hi ∈ S` with `lo < hi`, then on `[lo, hi]`

        f x ≤ f lo + (f hi - f lo)/(hi - lo) · (x - lo). -/
theorem conv_secant {S : Set ℝ} {f : ℝ → ℝ} {lo hi x : ℝ}
    (hfc : ConvexOn ℝ S f) (hlo : lo ∈ S) (hhi : hi ∈ S)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    f x ≤ f lo + (f hi - f lo) / (hi - lo) * (x - lo) := by
  have hd : 0 < hi - lo := by linarith
  set a := (hi - x) / (hi - lo) with ha
  set b := (x - lo) / (hi - lo) with hb
  have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
  have hb0 : 0 ≤ b := by rw [hb]; apply div_nonneg <;> linarith
  have hne : hi - lo ≠ 0 := by linarith
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hpt : a • lo + b • hi = x := by
    rw [ha, hb]; simp only [smul_eq_mul]; field_simp; ring
  have hconv := hfc.2 hlo hhi ha0 hb0 hab
  rw [hpt] at hconv
  simp only [smul_eq_mul] at hconv
  have hsec : a * f lo + b * f hi
      = f lo + (f hi - f lo) / (hi - lo) * (x - lo) := by
    rw [ha, hb]; field_simp; ring
  linarith [hconv, hsec.le, hsec.ge]

/-- **Generic tangent (upper) envelope for a CONCAVE function.**  Dual of
    `conv_tangent`: a concave function lies on/below its tangent at `lo`. -/
theorem conc_tangent {S : Set ℝ} {f : ℝ → ℝ} {lo d : ℝ}
    (hfc : ConcaveOn ℝ S f) (hlo : lo ∈ S) (hd : HasDerivAt f d lo)
    {x : ℝ} (hx : x ∈ S) (hle : lo ≤ x) :
    f x ≤ f lo + d * (x - lo) := by
  have hdual : HasDerivAt (fun y => -f y) (-d) lo := hd.neg
  have h := conv_tangent hfc.neg hlo hdual hx hle
  simp only [Pi.neg_apply] at h
  linarith [h]

/-- **Generic secant (lower) envelope for a CONCAVE function.**  Dual of
    `conv_secant`: a concave function lies on/above its chord. -/
theorem conc_secant {S : Set ℝ} {f : ℝ → ℝ} {lo hi x : ℝ}
    (hfc : ConcaveOn ℝ S f) (hlo : lo ∈ S) (hhi : hi ∈ S)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    f lo + (f hi - f lo) / (hi - lo) * (x - lo) ≤ f x := by
  have h := conv_secant hfc.neg hlo hhi hlt hx1 hx2
  simp only [Pi.neg_apply] at h
  have heq : (-f hi - -f lo) / (hi - lo) * (x - lo)
      = -((f hi - f lo) / (hi - lo) * (x - lo)) := by ring
  rw [heq] at h
  linarith [h]

/-! ## 1. Exponential activation envelopes. -/

/-- **`exp_lower` (tangent / LOWER envelope).**  For any anchor `xa` and any `x`,
    `exp` lies on/above its tangent line at `xa`:

        exp xa + exp xa · (x - xa) ≤ exp x.

    Holds for EVERY `x` (a convex function is above all of its tangents). -/
theorem exp_lower (xa x : ℝ) :
    Real.exp xa + Real.exp xa * (x - xa) ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - xa)
  have hpos := (Real.exp_pos xa).le
  have hmul := mul_le_mul_of_nonneg_left h hpos
  have hsplit : Real.exp xa * Real.exp (x - xa) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp xa + Real.exp xa * (x - xa)
      = Real.exp xa * ((x - xa) + 1) := by ring
    _ ≤ Real.exp xa * Real.exp (x - xa) := hmul
    _ = Real.exp x := hsplit

/-- **`exp_upper` (secant / UPPER envelope).**  On `[lo, hi]` (with `lo < hi`),
    `exp` lies on/below the secant through its endpoints. -/
theorem exp_upper (lo hi x : ℝ) (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.exp x ≤ Real.exp lo
      + (Real.exp hi - Real.exp lo) / (hi - lo) * (x - lo) :=
  conv_secant convexOn_exp (Set.mem_univ lo) (Set.mem_univ hi) hlt hx1 hx2

/-! ## 2. Sigmoid: S-shape (convex on `Iic 0`, concave on `Ici 0`). -/

/-- The defining identity in cleared form: `sigmoid x · (1 + exp (-x)) = 1`. -/
theorem sigmoid_clear (x : ℝ) : sigmoid x * (1 + Real.exp (-x)) = 1 := by
  rw [sigmoid_def]
  have hp : (0 : ℝ) < 1 + Real.exp (-x) := by positivity
  field_simp

/-- `sigmoid` is CONVEX on `(-∞, 0]`.  Proven from monotonicity of its
    derivative `s·(1-s)` (increasing while `s ≤ 1/2`). -/
theorem convexOn_sigmoid_Iic : ConvexOn ℝ (Iic 0) sigmoid := by
  apply MonotoneOn.convexOn_of_deriv (convex_Iic 0)
  · exact differentiable_sigmoid.continuous.continuousOn
  · exact differentiable_sigmoid.differentiableOn
  · rw [interior_Iic, deriv_sigmoid]
    intro a ha b hb hab
    simp only [mem_Iio] at ha hb
    dsimp only
    have hsa := sigmoid_pos a
    have hsb := sigmoid_pos b
    have hsa2 : sigmoid a ≤ 2⁻¹ := by rw [← sigmoid_zero]; exact sigmoid_le ha.le
    have hsb2 : sigmoid b ≤ 2⁻¹ := by rw [← sigmoid_zero]; exact sigmoid_le hb.le
    have hmono : sigmoid a ≤ sigmoid b := sigmoid_le hab
    nlinarith [hsa, hsb, hsa2, hsb2, hmono]

/-- `sigmoid` is CONCAVE on `[0, ∞)`.  Proven from antitonicity of its
    derivative `s·(1-s)` (decreasing while `s ≥ 1/2`). -/
theorem concaveOn_sigmoid_Ici : ConcaveOn ℝ (Ici 0) sigmoid := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact differentiable_sigmoid.continuous.continuousOn
  · exact differentiable_sigmoid.differentiableOn
  · rw [interior_Ici, deriv_sigmoid]
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    dsimp only
    have hsa := sigmoid_lt_one a
    have hsb := sigmoid_lt_one b
    have hsa2 : 2⁻¹ ≤ sigmoid a := by rw [← sigmoid_zero]; exact sigmoid_le ha.le
    have hsb2 : 2⁻¹ ≤ sigmoid b := by rw [← sigmoid_zero]; exact sigmoid_le hb.le
    have hmono : sigmoid a ≤ sigmoid b := sigmoid_le hab
    nlinarith [hsa, hsb, hsa2, hsb2, hmono]

/-! ### Sigmoid envelopes on the CONVEX half `[lo, hi] ⊆ (-∞, 0]`. -/

/-- **LOWER envelope (tangent at `lo`).**  On `[lo, hi]` with `hi ≤ 0`:

        sigmoid lo + sigmoid lo·(1 - sigmoid lo)·(x - lo) ≤ sigmoid x.

    The slope `sigmoid lo·(1-sigmoid lo) = (sigmoid)'(lo)`. -/
theorem sigmoid_lower_convex (lo hi x : ℝ) (hhi : hi ≤ 0)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    sigmoid lo + sigmoid lo * (1 - sigmoid lo) * (x - lo) ≤ sigmoid x := by
  have hloS : lo ∈ Iic (0:ℝ) := by simp only [mem_Iic]; linarith
  have hxS : x ∈ Iic (0:ℝ) := by simp only [mem_Iic]; linarith
  have hd : HasDerivAt sigmoid (sigmoid lo * (1 - sigmoid lo)) lo := by
    have := hasDerivAt_sigmoid lo
    convert this using 1
  exact conv_tangent convexOn_sigmoid_Iic hloS hd hxS hx1

/-- **UPPER envelope (secant).**  On `[lo, hi]` with `hi ≤ 0` and `lo < hi`:

        sigmoid x ≤ sigmoid lo + (sigmoid hi - sigmoid lo)/(hi - lo)·(x - lo). -/
theorem sigmoid_upper_convex (lo hi x : ℝ) (hhi : hi ≤ 0)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    sigmoid x ≤ sigmoid lo
      + (sigmoid hi - sigmoid lo) / (hi - lo) * (x - lo) := by
  have hloS : lo ∈ Iic (0:ℝ) := by simp only [mem_Iic]; linarith
  have hhiS : hi ∈ Iic (0:ℝ) := by simp only [mem_Iic]; linarith
  exact conv_secant convexOn_sigmoid_Iic hloS hhiS hlt hx1 hx2

/-! ### Sigmoid envelopes on the CONCAVE half `[lo, hi] ⊆ [0, ∞)`. -/

/-- **UPPER envelope (tangent at `lo`).**  On `[lo, hi]` with `0 ≤ lo`:

        sigmoid x ≤ sigmoid lo + sigmoid lo·(1 - sigmoid lo)·(x - lo). -/
theorem sigmoid_upper_concave (lo hi x : ℝ) (hlo : 0 ≤ lo)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    sigmoid x ≤ sigmoid lo + sigmoid lo * (1 - sigmoid lo) * (x - lo) := by
  have hloS : lo ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
  have hxS : x ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
  have hd : HasDerivAt sigmoid (sigmoid lo * (1 - sigmoid lo)) lo :=
    hasDerivAt_sigmoid lo
  exact conc_tangent concaveOn_sigmoid_Ici hloS hd hxS hx1

/-- **LOWER envelope (secant).**  On `[lo, hi]` with `0 ≤ lo` and `lo < hi`:

        sigmoid lo + (sigmoid hi - sigmoid lo)/(hi - lo)·(x - lo) ≤ sigmoid x. -/
theorem sigmoid_lower_concave (lo hi x : ℝ) (hlo : 0 ≤ lo)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    sigmoid lo + (sigmoid hi - sigmoid lo) / (hi - lo) * (x - lo)
      ≤ sigmoid x := by
  have hloS : lo ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
  have hhiS : hi ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
  exact conc_secant concaveOn_sigmoid_Ici hloS hhiS hlt hx1 hx2

/-! ## 3. Tanh via the sigmoid identity `tanh x = 2·sigmoid (2x) - 1`. -/

/-- `tanh x = 2·sigmoid (2x) - 1`.  An exact affine reparametrization of the
    logistic, so all of `tanh`'s convexity / envelope structure transfers. -/
theorem tanh_eq_sigmoid (x : ℝ) : Real.tanh x = 2 * sigmoid (2 * x) - 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, sigmoid_def]
  have hexp : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [hexp]
  have hpos : (0:ℝ) < 1 + Real.exp (-x) * Real.exp (-x) := by positivity
  have hpos2 : (0:ℝ) < (Real.exp x + Real.exp (-x)) / 2 := by positivity
  field_simp
  nlinarith [hex, Real.exp_pos x, Real.exp_pos (-x)]

/-- Auxiliary: the `tanh` secant slope over `[lo, hi]` equals `2 ·` the
    `sigmoid` secant slope over `[2lo, 2hi]`, evaluated at the matching offset.
    This lets every `tanh` envelope reduce to the corresponding `sigmoid` one,
    with no fresh analysis. -/
private theorem tanh_secant_rescale (lo hi x : ℝ) (hlt : lo < hi) :
    2 * ((sigmoid (2 * hi) - sigmoid (2 * lo)) / (2 * hi - 2 * lo) * (2 * x - 2 * lo))
      = (Real.tanh hi - Real.tanh lo) / (hi - lo) * (x - lo) := by
  have hd : hi - lo ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hd2 : (2:ℝ) * hi - 2 * lo ≠ 0 := by intro h; apply hd; linarith
  rw [tanh_eq_sigmoid hi, tanh_eq_sigmoid lo]
  field_simp
  ring

/-- **`tanh` UPPER envelope (secant) on the convex half** `[lo, hi] ⊆ (-∞, 0]`.
    Reduced from `sigmoid_upper_convex` at the doubled points. -/
theorem tanh_upper_convex (lo hi x : ℝ) (hhi : hi ≤ 0)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh x ≤ Real.tanh lo
      + (Real.tanh hi - Real.tanh lo) / (hi - lo) * (x - lo) := by
  have hs := sigmoid_upper_convex (2 * lo) (2 * hi) (2 * x)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [← tanh_secant_rescale lo hi x hlt, tanh_eq_sigmoid x, tanh_eq_sigmoid lo]
  linarith [hs]

/-- **`tanh` LOWER envelope (tangent at `lo`) on the convex half**
    `[lo, hi] ⊆ (-∞, 0]`.  Reduced from `sigmoid_lower_convex`; the slope is
    `4·sigmoid (2lo)·(1 - sigmoid (2lo)) = (tanh)'(lo)`. -/
theorem tanh_lower_convex (lo hi x : ℝ) (hhi : hi ≤ 0)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh lo
      + 4 * sigmoid (2 * lo) * (1 - sigmoid (2 * lo)) * (x - lo) ≤ Real.tanh x := by
  have hs := sigmoid_lower_convex (2 * lo) (2 * hi) (2 * x)
    (by linarith) (by linarith) (by linarith)
  rw [tanh_eq_sigmoid x, tanh_eq_sigmoid lo]
  nlinarith [hs]

/-- **`tanh` LOWER envelope (secant) on the concave half** `[lo, hi] ⊆ [0, ∞)`.
    Reduced from `sigmoid_lower_concave`. -/
theorem tanh_lower_concave (lo hi x : ℝ) (hlo : 0 ≤ lo)
    (hlt : lo < hi) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh lo
      + (Real.tanh hi - Real.tanh lo) / (hi - lo) * (x - lo) ≤ Real.tanh x := by
  have hs := sigmoid_lower_concave (2 * lo) (2 * hi) (2 * x)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [← tanh_secant_rescale lo hi x hlt, tanh_eq_sigmoid x, tanh_eq_sigmoid lo]
  linarith [hs]

/-- **`tanh` UPPER envelope (tangent at `lo`) on the concave half**
    `[lo, hi] ⊆ [0, ∞)`.  Reduced from `sigmoid_upper_concave`. -/
theorem tanh_upper_concave (lo hi x : ℝ) (hlo : 0 ≤ lo)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh x ≤ Real.tanh lo
      + 4 * sigmoid (2 * lo) * (1 - sigmoid (2 * lo)) * (x - lo) := by
  have hs := sigmoid_upper_concave (2 * lo) (2 * hi) (2 * x)
    (by linarith) (by linarith) (by linarith)
  rw [tanh_eq_sigmoid x, tanh_eq_sigmoid lo]
  nlinarith [hs]

/-! ## 4. Tanh-approximation GELU.

    `geluTanh x = ½·x·(1 + tanh (√(2/π)·(x + 0.044715·x³)))`.

  The inner `tanh ∈ [-1, 1]`, so `1 + tanh ∈ [0, 2]`.  This gives the sound
  (if loose) sign-split linear envelopes
      x ≥ 0 :  0 ≤ geluTanh x ≤ x,
      x ≤ 0 :  x ≤ geluTanh x ≤ 0.
  These are exactly the affine bounds a CROWN pass falls back to when a tight
  envelope for the composite is unavailable, and they are fully proven here. -/

/-- The tanh-approximation GELU. -/
noncomputable def geluTanh (x : ℝ) : ℝ :=
  (1 / 2) * x * (1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)))

/-- The inner factor `1 + tanh (·)` lies in `[0, 2]`. -/
theorem gelu_inner_mem (x : ℝ) :
    0 ≤ 1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3))
    ∧ 1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)) ≤ 2 := by
  have h1 := Real.neg_one_lt_tanh
    (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3))
  have h2 := Real.tanh_lt_one
    (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3))
  constructor <;> linarith

/-- **GELU envelopes on the nonnegative half.**  For `x ≥ 0`:
    `0 ≤ geluTanh x ≤ x`. -/
theorem gelu_envelope_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ geluTanh x ∧ geluTanh x ≤ x := by
  obtain ⟨hlo, hhi⟩ := gelu_inner_mem x
  unfold geluTanh
  constructor
  · positivity
  · nlinarith [hlo, hhi, hx]

/-- **GELU envelopes on the nonpositive half.**  For `x ≤ 0`:
    `x ≤ geluTanh x ≤ 0`. -/
theorem gelu_envelope_nonpos (x : ℝ) (hx : x ≤ 0) :
    x ≤ geluTanh x ∧ geluTanh x ≤ 0 := by
  obtain ⟨hlo, hhi⟩ := gelu_inner_mem x
  unfold geluTanh
  constructor
  · nlinarith [hlo, hhi, hx]
  · nlinarith [hlo, hhi, hx]

/-! ## 5. Trust-base check.  Each must list ONLY the three standard logical
    axioms `[propext, Classical.choice, Quot.sound]`. -/

#print axioms conv_tangent
#print axioms conv_secant
#print axioms conc_tangent
#print axioms conc_secant
#print axioms exp_lower
#print axioms exp_upper
#print axioms sigmoid_clear
#print axioms convexOn_sigmoid_Iic
#print axioms concaveOn_sigmoid_Ici
#print axioms sigmoid_lower_convex
#print axioms sigmoid_upper_convex
#print axioms sigmoid_upper_concave
#print axioms sigmoid_lower_concave
#print axioms tanh_eq_sigmoid
#print axioms tanh_upper_convex
#print axioms tanh_lower_convex
#print axioms tanh_lower_concave
#print axioms tanh_upper_concave
#print axioms geluTanh
#print axioms gelu_inner_mem
#print axioms gelu_envelope_nonneg
#print axioms gelu_envelope_nonpos

end Crownproof
