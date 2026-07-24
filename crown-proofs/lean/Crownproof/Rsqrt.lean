/-
  LayerNorm normalizing-nonlinearity CROWN envelopes, formalized in Lean 4
  over the reals, using mathlib.

  The LayerNorm "normalize" step divides by the standard deviation, i.e. it
  applies the reciprocal-square-root nonlinearity

        f(v) = 1 / Real.sqrt (v + eps),      eps > 0,  v + eps > 0.

  Over `v ∈ [vlo, vhi]` with `vlo + eps > 0`, `f` is positive, strictly
  decreasing, and CONVEX.  CROWN relaxes such a unary nonlinearity by a pair of
  linear bounds; soundness of that relaxation is exactly:

    * `rsqrt_upper` : a convex function lies BELOW its chord, so `f` is at most
        the SECANT line through the two endpoints `(vlo, f vlo), (vhi, f vhi)`.
        This is the UPPER linear envelope CROWN emits.

    * `rsqrt_lower` : a convex function lies ABOVE each of its TANGENTS, so `f`
        is at least the tangent line at any anchor point `va`
        (`f'(va) = -½ (va+eps)^{-3/2} = -½ (f va)^3`).
        This is the LOWER linear envelope CROWN emits.

  Strategy.  We deliberately AVOID heavy convex-analysis machinery.  We use the
  IMPLICIT characterization of the value `t = f(v)`:

        t > 0      and      t^2 * (v + eps) = 1.

  All three relevant points `(t, tlo, thi)` / `(t, ta)` satisfy this, and the
  envelope inequalities, after clearing the (positive) denominators via these
  defining identities, become POLYNOMIAL inequalities that factor as a product
  of manifestly-signed terms:

      secant :  (t^2 tlo^2 thi^2) · (secant defect)
                  = -(t-thi)(tlo-t)(tlo-thi)(t·thi+t·tlo+thi·tlo)        ≤ 0
      tangent:  2 (t^2 ta^2) · (tangent defect)
                  = -(ta^2 (t-ta)^2 (2t+ta))                            ≤ 0

  Each identity is discharged by `linear_combination` against the defining
  identities; the sign of the right-hand side is `positivity`/ordering; and the
  positive leading factor lets `nlinarith` divide it out.  No `sorry`.

  Only `Mathlib.Analysis.SpecialFunctions.Sqrt` (already built in this project)
  is added beyond the usual tactic imports; everything else is ordered-field /
  polynomial reasoning.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic

namespace Crownproof

open Real

/-- The LayerNorm normalizing nonlinearity `f(v) = 1 / √(v + eps)`. -/
noncomputable def rsqrt (eps v : ℝ) : ℝ := 1 / Real.sqrt (v + eps)

/-! ## 1. Defining facts of `rsqrt` (the implicit characterization). -/

/-- `rsqrt` is positive whenever its argument is in the domain `v + eps > 0`. -/
theorem rsqrt_pos (eps v : ℝ) (hw : 0 < v + eps) : 0 < rsqrt eps v := by
  unfold rsqrt
  have hs := Real.sqrt_pos.mpr hw
  positivity

/-- The defining identity: `t = rsqrt eps v` satisfies `t^2 * (v + eps) = 1`. -/
theorem rsqrt_sq (eps v : ℝ) (hw : 0 < v + eps) :
    (rsqrt eps v) ^ 2 * (v + eps) = 1 := by
  unfold rsqrt
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hw)]
  field_simp

/-- `rsqrt` is decreasing: larger `v` gives a smaller value (it is `1/√·`).
    This is itself proven from the implicit characterization, sorry-free. -/
theorem rsqrt_antitone (eps v v' : ℝ)
    (hw : 0 < v + eps) (hw' : 0 < v' + eps) (hle : v ≤ v') :
    rsqrt eps v' ≤ rsqrt eps v := by
  have ht := rsqrt_pos eps v hw
  have ht' := rsqrt_pos eps v' hw'
  have e := rsqrt_sq eps v hw
  have e' := rsqrt_sq eps v' hw'
  nlinarith [mul_pos ht ht',
             mul_nonneg (le_of_lt (mul_pos ht ht')) (sub_nonneg.2 hle),
             mul_pos (mul_pos ht ht') hw']

/-! ## 2. Abstract cleared polynomial envelopes.

These are the pure algebraic cores: given three (resp. two) points satisfying
the implicit identity `t^2 * a = 1` (with `a = v + eps`), the secant / tangent
defects have a definite sign.  They are stated abstractly so the analytic part
(`rsqrt`) only needs to supply the identities. -/

/-- **Secant (upper) core, cleared.**  With `a, alo, ahi` the three (positive)
    shifted inputs and `t, tlo, thi` the corresponding values
    (`t^2·a = 1`, etc.), if `thi ≤ t ≤ tlo` (the decreasing order forced by
    `alo ≤ a ≤ ahi`), then

        t·(ahi - alo)  ≤  tlo·(ahi - a) + thi·(a - alo).

    Dividing by `(ahi - alo) = (vhi - vlo) > 0` this is exactly `f ≤ secant`. -/
theorem secant_cleared (t tlo thi a alo ahi : ℝ)
    (ht : 0 < t) (htlo : 0 < tlo) (hthi : 0 < thi)
    (ea : t ^ 2 * a = 1) (ealo : tlo ^ 2 * alo = 1) (eahi : thi ^ 2 * ahi = 1)
    (h1 : thi ≤ t) (h2 : t ≤ tlo) :
    t * (ahi - alo) ≤ tlo * (ahi - a) + thi * (a - alo) := by
  -- The signed factorization of the cleared secant defect.
  have key : 0 ≤ (t - thi) * (tlo - t) *
      ((tlo - thi) * (t * thi + t * tlo + thi * tlo)) := by
    apply mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2))
    apply mul_nonneg (sub_nonneg.2 (le_trans h1 h2))
    positivity
  have M : (0 : ℝ) < t ^ 2 * tlo ^ 2 * thi ^ 2 := by positivity
  -- (t^2 tlo^2 thi^2) · (secant defect) = -(signed factorization).
  have ident :
      (t ^ 2 * tlo ^ 2 * thi ^ 2) *
        (t * (ahi - alo) - (tlo * (ahi - a) + thi * (a - alo)))
        = -((t - thi) * (tlo - t) *
            ((tlo - thi) * (t * thi + t * tlo + thi * tlo))) := by
    linear_combination (-thi ^ 2 * tlo ^ 2 * (thi - tlo)) * ea
      + (-t ^ 2 * thi ^ 2 * (t - thi)) * ealo
      + (t ^ 2 * tlo ^ 2 * (t - tlo)) * eahi
  nlinarith [ident, key, M]

/-- **Tangent (lower) core, cleared.**  With `a` the shifted input and `aa` the
    shifted anchor (both positive), and `t, ta` the values (`t^2·a = 1`,
    `ta^2·aa = 1`):

        ta - ½·ta^3·(a - aa)  ≤  t.

    Since `a - aa = v - va`, the left side is the tangent line at the anchor,
    so this is exactly `tangent ≤ f`.  No ordering hypothesis is needed: a
    convex function lies above every tangent on the whole domain. -/
theorem tangent_cleared (t ta a aa : ℝ)
    (ht : 0 < t) (hta : 0 < ta)
    (ea : t ^ 2 * a = 1) (eaa : ta ^ 2 * aa = 1) :
    ta - (1 / 2) * ta ^ 3 * (a - aa) ≤ t := by
  have key : 0 ≤ ta ^ 2 * (t - ta) ^ 2 * (2 * t + ta) := by positivity
  have M : (0 : ℝ) < t ^ 2 * ta ^ 2 := by positivity
  -- 2·(t^2 ta^2)·(tangent defect) = -(perfect-square factorization).
  have ident :
      (2 : ℝ) * (t ^ 2 * ta ^ 2) * ((ta - (1 / 2) * ta ^ 3 * (a - aa)) - t)
        = -(ta ^ 2 * (t - ta) ^ 2 * (2 * t + ta)) := by
    linear_combination (-ta ^ 5) * ea + (t ^ 2 * ta ^ 3) * eaa
  nlinarith [ident, key, M]

/-! ## 3. Main soundness theorems for `rsqrt`. -/

/--
**`rsqrt_upper` (secant / UPPER envelope).**
On `[vlo, vhi]` (with `vlo + eps > 0` and `vlo < vhi`), the convex function
`f(v) = 1/√(v+eps)` lies on or below the secant line through its two endpoints:

    rsqrt eps v
      ≤ rsqrt eps vlo
        + (rsqrt eps vhi - rsqrt eps vlo) / (vhi - vlo) * (v - vlo).

This is the sound UPPER linear bound CROWN uses for the LayerNorm normalizer.
-/
theorem rsqrt_upper (eps vlo vhi v : ℝ)
    (hlo : 0 < vlo + eps) (hlt : vlo < vhi)
    (hv1 : vlo ≤ v) (hv2 : v ≤ vhi) :
    rsqrt eps v ≤ rsqrt eps vlo
      + (rsqrt eps vhi - rsqrt eps vlo) / (vhi - vlo) * (v - vlo) := by
  have hhi : 0 < vhi + eps := by linarith
  have hwv : 0 < v + eps := by linarith
  have t := rsqrt_pos eps v hwv
  have tlo := rsqrt_pos eps vlo hlo
  have thi := rsqrt_pos eps vhi hhi
  have ev := rsqrt_sq eps v hwv
  have elo := rsqrt_sq eps vlo hlo
  have ehi := rsqrt_sq eps vhi hhi
  -- decreasing order  thi ≤ t ≤ tlo  forced by  vlo ≤ v ≤ vhi.
  have h1 : rsqrt eps vhi ≤ rsqrt eps v := rsqrt_antitone eps v vhi hwv hhi hv2
  have h2 : rsqrt eps v ≤ rsqrt eps vlo := rsqrt_antitone eps vlo v hlo hwv hv1
  -- cleared secant inequality from the abstract core (a = v+eps, etc.).
  have hineq :
      rsqrt eps v * ((vhi + eps) - (vlo + eps))
        ≤ rsqrt eps vlo * ((vhi + eps) - (v + eps))
          + rsqrt eps vhi * ((v + eps) - (vlo + eps)) :=
    secant_cleared (rsqrt eps v) (rsqrt eps vlo) (rsqrt eps vhi)
      (v + eps) (vlo + eps) (vhi + eps) t tlo thi ev elo ehi h1 h2
  have hineq' :
      rsqrt eps v * (vhi - vlo)
        ≤ rsqrt eps vlo * (vhi - v) + rsqrt eps vhi * (v - vlo) := by
    nlinarith [hineq]
  -- convert the cleared inequality to the division form.
  have hd : 0 < vhi - vlo := by linarith
  rw [div_mul_eq_mul_div, ← sub_le_iff_le_add', le_div_iff₀ hd]
  nlinarith [hineq']

/--
**`rsqrt_lower` (tangent / LOWER envelope).**
For any anchor `va` in the domain (`va + eps > 0`) and any `v` in the domain
(`v + eps > 0`), the convex function `f(v) = 1/√(v+eps)` lies on or above its
tangent line at `va`:

    rsqrt eps va - ½ · (rsqrt eps va)^3 · (v - va)  ≤  rsqrt eps v.

The slope `-½ (rsqrt eps va)^3 = -½ (va+eps)^{-3/2} = f'(va)`.  This is the
sound LOWER linear bound CROWN uses for the LayerNorm normalizer.  It holds for
EVERY `v` in the domain (a convex function is above all of its tangents), so in
particular on any box `[vlo, vhi]` with `vlo + eps > 0`; taking `va := vlo`
gives the lower-endpoint tangent that pairs with `rsqrt_upper`.
-/
theorem rsqrt_lower (eps va v : ℝ)
    (hva : 0 < va + eps) (hwv : 0 < v + eps) :
    rsqrt eps va - (1 / 2) * (rsqrt eps va) ^ 3 * (v - va) ≤ rsqrt eps v := by
  have t := rsqrt_pos eps v hwv
  have ta := rsqrt_pos eps va hva
  have ev := rsqrt_sq eps v hwv
  have ea := rsqrt_sq eps va hva
  -- the abstract tangent core with a = v+eps, aa = va+eps;  a - aa = v - va.
  have h := tangent_cleared (rsqrt eps v) (rsqrt eps va) (v + eps) (va + eps)
              t ta ev ea
  -- (v+eps) - (va+eps) = v - va
  have heq : (v + eps) - (va + eps) = v - va := by ring
  rw [heq] at h
  exact h

/-! ## 4. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms rsqrt_pos
#print axioms rsqrt_sq
#print axioms rsqrt_antitone
#print axioms secant_cleared
#print axioms tangent_cleared
#print axioms rsqrt_upper
#print axioms rsqrt_lower

end Crownproof
