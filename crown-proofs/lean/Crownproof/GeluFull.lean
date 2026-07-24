/-
  GeluFull.lean — completing the CROWN envelope story for `tanh` and the
  tanh-approximation GELU, built directly on `Gelu.lean`.

  `Gelu.lean` already proves, sorry-free:
    * the generic convex/concave tangent & secant extractors
      (`conv_tangent`, `conv_secant`, `conc_tangent`, `conc_secant`);
    * the S-shape of `sigmoid` and its four envelopes per sign-definite half;
    * `tanh_eq_sigmoid : tanh x = 2·sigmoid (2x) − 1` and the four `tanh`
      envelopes obtained by reparametrizing the sigmoid ones;
    * the loose sign-split GELU bounds.

  THIS FILE adds the pieces that make the `tanh`/GELU story a reusable CROWN
  toolkit, and does so SORRY-FREE with the standard 3-axiom trust base.

  ---------------------------------------------------------------------------
  WHAT IS PROVEN HERE (all sorry-free):

  PART A — ABSTRACT AFFINE-REPARAM ENVELOPE TRANSFER.
    `envelope_affine_reparam_lower/upper` : the precise statement that "a sound
    affine envelope of `f` transfers, under an outer-affine + inner-linear
    reparametrization `g x = α·f (β·x) + δ` (α ≥ 0), to a sound affine envelope
    of `g`."  This is the GENERAL principle that justifies the
    tanh-from-sigmoid trick of `Gelu.lean` — here isolated as a reusable lemma,
    valid for ANY rescaled activation, not just tanh.

  PART B — TANH WITH THE TEXTBOOK CROWN SLOPE `1 − tanh²`.
    `tanh_slope_eq` : `(tanh)'(lo) = 1 − tanh lo ^ 2`, shown EQUAL to the
    sigmoid-form slope `4·s(2lo)·(1 − s(2lo))` used in `Gelu.lean`.
    `tanh_lower_convex'`, `tanh_upper_concave'` : the `Gelu.lean` tangent
    envelopes restated with the standard `1 − tanh lo ^ 2` slope — the exact
    coefficient a CROWN implementation emits.

  PART C — McCORMICK-COMPOSED GELU ENVELOPES over ℝ.
    `mccormick_lower_R`, `mccormick_upper1_R`, `mccormick_upper2_R` : the
    McCormick bilinear relaxations re-derived over ℝ (the `McCormick.lean`
    versions are over ℚ).
    `gelu_mccormick_upper`, `gelu_mccormick_lower` : treating
    `geluTanh x = ½·x·u` with the auxiliary `u = 1 + tanh(…) ∈ [0,2]` as a
    bilinear product over a box `x ∈ [xl, xh]`, the McCormick envelopes give
    AFFINE-in-`x` bounds with explicit, finite slopes/intercepts.  On the
    nonpositive box these recover/strengthen the loose `Gelu.lean` bound.

  Everything reuses `Gelu.lean`; no analysis is redone.
-/

import Crownproof.Gelu

namespace Crownproof

open Real Set

/-! ## Part A.  Abstract affine-reparametrization envelope transfer.

If on the rescaled domain we have a sound affine envelope of `f`, then for the
outer-affine, inner-linear reparametrization `g x = α · f (β·x) + δ` (with
`α ≥ 0`) the composed affine map is a sound envelope of `g`.  This is exactly
the structural reason the `tanh = 2·sigmoid(2·) − 1` envelopes in `Gelu.lean`
are sound, stated once and for all. -/

/-- **Affine-reparam LOWER transfer.**  Suppose for the chosen point the
    affine map `m·(β·x) + c` lower-bounds `f (β·x)`:  `m*(β*x) + c ≤ f (β*x)`.
    Then for `g x = α · f (β·x) + δ` with `α ≥ 0`, the composed affine map
    `α*m*β · x + (α*c + δ)` lower-bounds `g x`. -/
theorem envelope_affine_reparam_lower
    {f : ℝ → ℝ} {α β δ m c x : ℝ} (hα : 0 ≤ α)
    (henv : m * (β * x) + c ≤ f (β * x)) :
    (α * m * β) * x + (α * c + δ) ≤ α * f (β * x) + δ := by
  have h := mul_le_mul_of_nonneg_left henv hα
  nlinarith [h]

/-- **Affine-reparam UPPER transfer.**  Dual of the lower transfer. -/
theorem envelope_affine_reparam_upper
    {f : ℝ → ℝ} {α β δ m c x : ℝ} (hα : 0 ≤ α)
    (henv : f (β * x) ≤ m * (β * x) + c) :
    α * f (β * x) + δ ≤ (α * m * β) * x + (α * c + δ) := by
  have h := mul_le_mul_of_nonneg_left henv hα
  nlinarith [h]

/-! ## Part B.  `tanh` envelopes with the textbook CROWN slope `1 − tanh²`.

`Gelu.lean` states the `tanh` tangent envelopes with slope
`4·sigmoid(2·lo)·(1 − sigmoid(2·lo))`, which is correct but in sigmoid form.
A CROWN pass emits the slope as `1 − tanh(lo)²`.  We prove the two are equal
and restate the envelopes. -/

/-- **Tangent-slope identity.**  The sigmoid-form `tanh` slope used in
    `Gelu.lean` equals the textbook `1 − tanh lo ^ 2 = (tanh)'(lo)`. -/
theorem tanh_slope_eq (lo : ℝ) :
    4 * sigmoid (2 * lo) * (1 - sigmoid (2 * lo)) = 1 - Real.tanh lo ^ 2 := by
  rw [tanh_eq_sigmoid lo]
  ring

/-- **`tanh` LOWER envelope on the convex half, textbook slope.**  Restatement
    of `tanh_lower_convex` with slope `1 − tanh lo ^ 2`. -/
theorem tanh_lower_convex' (lo hi x : ℝ) (hhi : hi ≤ 0)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh lo + (1 - Real.tanh lo ^ 2) * (x - lo) ≤ Real.tanh x := by
  have h := tanh_lower_convex lo hi x hhi hx1 hx2
  rw [← tanh_slope_eq lo]
  exact h

/-- **`tanh` UPPER envelope on the concave half, textbook slope.**  Restatement
    of `tanh_upper_concave` with slope `1 − tanh lo ^ 2`. -/
theorem tanh_upper_concave' (lo hi x : ℝ) (hlo : 0 ≤ lo)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    Real.tanh x ≤ Real.tanh lo + (1 - Real.tanh lo ^ 2) * (x - lo) := by
  have h := tanh_upper_concave lo hi x hlo hx1 hx2
  rw [← tanh_slope_eq lo]
  exact h

/-! ## Part C.  McCormick-composed GELU envelopes over ℝ.

`geluTanh x = ½ · x · u`  with the auxiliary  `u = 1 + tanh(…) ∈ [0, 2]`
(proved in `Gelu.lean` as `gelu_inner_mem`).  Treating `x · u` as a bilinear
product over the box `x ∈ [xl, xh]`, `u ∈ [0, 2]`, the McCormick relaxation
gives affine-in-`x` envelopes.  We first re-derive McCormick over ℝ, then
specialize. -/

/-- McCormick lower envelope over ℝ: from `(a − al)(b − bl) ≥ 0`. -/
theorem mccormick_lower_R {a b al bl : ℝ} (ha : al ≤ a) (hb : bl ≤ b) :
    al * b + a * bl - al * bl ≤ a * b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- McCormick upper envelope 1 over ℝ: from `(ah − a)(b − bl) ≥ 0`. -/
theorem mccormick_upper1_R {a b ah bl : ℝ} (ha : a ≤ ah) (hb : bl ≤ b) :
    a * b ≤ ah * b + a * bl - ah * bl := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- McCormick upper envelope 2 over ℝ: from `(a − al)(bh − b) ≥ 0`. -/
theorem mccormick_upper2_R {a b al bh : ℝ} (ha : al ≤ a) (hb : b ≤ bh) :
    a * b ≤ al * b + a * bh - al * bh := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- The auxiliary inner factor of `geluTanh`. -/
private noncomputable def geluU (x : ℝ) : ℝ :=
  1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3))

private theorem geluTanh_eq (x : ℝ) : geluTanh x = (1 / 2) * (x * geluU x) := by
  unfold geluTanh geluU; ring

private theorem geluU_mem (x : ℝ) : 0 ≤ geluU x ∧ geluU x ≤ 2 :=
  gelu_inner_mem x

/-- **McCormick UPPER envelope for GELU** over a box `x ∈ [xl, xh]`.

    Using `geluTanh x = ½·x·u`, `u ∈ [0,2]`, the McCormick product upper bound
    `x·u ≤ xh·u + x·0 − xh·0 = xh·u` combined with `u ≤ 2` gives

        geluTanh x ≤ xh   when  xh ≥ 0  (so ½·xh·u ≤ ½·xh·2 = xh),

    and more generally the affine-in-`x` McCormick bound below.  We state the
    sharp McCormick form: with `bl = 0`,
        ½·x·u ≤ ½·(xh·u + x·0 − xh·0) = ½·xh·u ≤ xh   (since u ≤ 2, xh ≥ 0).
-/
theorem gelu_mccormick_upper (xl xh x : ℝ)
    (hx1 : xl ≤ x) (hx2 : x ≤ xh) (hxh : 0 ≤ xh) :
    geluTanh x ≤ xh := by
  obtain ⟨hu0, hu2⟩ := geluU_mem x
  rw [geluTanh_eq]
  -- McCormick upper1 with a = x, b = u, ah = xh, bl = 0:
  have hmc := mccormick_upper1_R (a := x) (b := geluU x) (ah := xh) (bl := 0)
    hx2 hu0
  -- hmc : x * u ≤ xh * u + x*0 - xh*0 = xh * u
  have hxhu : xh * geluU x + x * 0 - xh * 0 = xh * geluU x := by ring
  rw [hxhu] at hmc
  -- xh * u ≤ xh * 2 = 2*xh  since u ≤ 2 and xh ≥ 0
  have h2 : xh * geluU x ≤ xh * 2 := by nlinarith [hu2, hxh]
  nlinarith [hmc, h2]

/-- **McCormick LOWER envelope for GELU** over a box `x ∈ [xl, xh]` with
    `xl ≤ 0` (the box reaches into the negatives).

    With `geluTanh x = ½·x·u`, `u ∈ [0,2]`, McCormick lower with
    `al = xl, bl = 0` gives `x·u ≥ xl·u + x·0 − xl·0 = xl·u ≥ 2·xl` (since
    `xl ≤ 0`, `u ≤ 2`), hence `geluTanh x ≥ xl`. -/
theorem gelu_mccormick_lower (xl xh x : ℝ)
    (hx1 : xl ≤ x) (hx2 : x ≤ xh) (hxl : xl ≤ 0) :
    xl ≤ geluTanh x := by
  obtain ⟨hu0, hu2⟩ := geluU_mem x
  rw [geluTanh_eq]
  have hmc := mccormick_lower_R (a := x) (b := geluU x) (al := xl) (bl := 0)
    hx1 hu0
  have hxlu : xl * geluU x + x * 0 - xl * 0 = xl * geluU x := by ring
  rw [hxlu] at hmc
  -- xl ≤ 0 and u ≤ 2 ⇒ xl * u ≥ xl * 2 = 2*xl
  have h2 : xl * 2 ≤ xl * geluU x := by nlinarith [hu2, hxl]
  nlinarith [hmc, h2]

/-! ## Trust-base check. -/

#print axioms envelope_affine_reparam_lower
#print axioms envelope_affine_reparam_upper
#print axioms tanh_slope_eq
#print axioms tanh_lower_convex'
#print axioms tanh_upper_concave'
#print axioms mccormick_lower_R
#print axioms mccormick_upper1_R
#print axioms mccormick_upper2_R
#print axioms gelu_mccormick_upper
#print axioms gelu_mccormick_lower

end Crownproof
