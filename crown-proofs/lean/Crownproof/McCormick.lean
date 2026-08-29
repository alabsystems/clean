/-
  McCormick bilinear envelopes for a product  p = a * b  over the rationals (ℚ),
  with  a ∈ [al, ah]  and  b ∈ [bl, bh].

  These are the four sound linear relaxations of a bilinear step (e.g. the
  (centered) * (rsqrt) multiplication inside the LayerNorm CROWN relaxation).
  Each follows in one line from the nonnegativity of a product of two
  nonnegative (resp. nonpositive) factors, via `nlinarith`.

      lower1 :  al·b + a·bl − al·bl ≤ a·b      from (a−al)(b−bl) ≥ 0
      lower2 :  ah·b + a·bh − ah·bh ≤ a·b      from (ah−a)(bh−b) ≥ 0
      upper1 :  a·b ≤ ah·b + a·bl − ah·bl      from (ah−a)(b−bl) ≥ 0
      upper2 :  a·b ≤ al·b + a·bh − al·bh      from (a−al)(bh−b) ≥ 0

  All arithmetic is over `Rat`, a `LinearOrderedField`, so these are pure
  ordered-field facts.  Proved sorry-free; trust base reported by
  `#print axioms` at the bottom.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Crownproof

/-- McCormick lower envelope 1: from `(a − al)(b − bl) ≥ 0`. -/
theorem mccormick_lower1 {a b al bl ah bh : ℚ}
    (ha : al ≤ a) (hb : bl ≤ b) :
    al * b + a * bl - al * bl ≤ a * b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- McCormick lower envelope 2: from `(ah − a)(bh − b) ≥ 0`. -/
theorem mccormick_lower2 {a b al bl ah bh : ℚ}
    (ha : a ≤ ah) (hb : b ≤ bh) :
    ah * b + a * bh - ah * bh ≤ a * b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- McCormick upper envelope 1: from `(ah − a)(b − bl) ≥ 0`. -/
theorem mccormick_upper1 {a b al bl ah bh : ℚ}
    (ha : a ≤ ah) (hb : bl ≤ b) :
    a * b ≤ ah * b + a * bl - ah * bl := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- McCormick upper envelope 2: from `(a − al)(bh − b) ≥ 0`. -/
theorem mccormick_upper2 {a b al bl ah bh : ℚ}
    (ha : al ≤ a) (hb : b ≤ bh) :
    a * b ≤ al * b + a * bh - al * bh := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end Crownproof

#print axioms Crownproof.mccormick_lower1
#print axioms Crownproof.mccormick_lower2
#print axioms Crownproof.mccormick_upper1
#print axioms Crownproof.mccormick_upper2
