/-
  Quadratic (pow2) interval envelopes for a square  s = t²  over the
  rationals (ℚ), with  t ∈ [l, u].

  These are the two sound linear relaxations of a squaring step — the premise
  classes NY's ground-truth dominance certifier emits for a quadratic
  ground-truth side (the sphere / cylinder / cone residual builders use
  `PowConstant(2)`; see `ny/crates/ny-groundtruth/src/cert.rs`).  Each follows
  in one line from the nonnegativity of a product, via `nlinarith`:

      tangent :  2c·t − c² ≤ t²             from (t − c)² ≥ 0       (any t, any c)
      secant  :  t² ≤ (l+u)·t − l·u         from (t − l)(u − t) ≥ 0 (t ∈ [l,u])

  The tangent at `c` is a supporting line of the convex parabola `s = t²`, so
  it is valid for EVERY rational `t` — no interval hypothesis.  The secant is
  the chord through `(l, l²)` and `(u, u²)`, an upper bound exactly on the box.
  All arithmetic is over `Rat`, a `LinearOrderedField`, so these are pure
  ordered-field facts.  Proved sorry-free; trust base reported by
  `#print axioms` at the bottom.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Crownproof

/-- Tangent lower envelope of the square: from `(t − c)² ≥ 0`.  Valid for
every `t` and every tangency point `c` — no interval hypothesis needed. -/
theorem pow2_tangent (t c : ℚ) :
    2 * c * t - c ^ 2 ≤ t ^ 2 := by
  nlinarith [sq_nonneg (t - c)]

/-- Secant upper envelope of the square on `[l, u]`: from `(t − l)(u − t) ≥ 0`. -/
theorem pow2_secant {t l u : ℚ}
    (hl : l ≤ t) (hu : t ≤ u) :
    t ^ 2 ≤ (l + u) * t - l * u := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)]

end Crownproof

#print axioms Crownproof.pow2_tangent
#print axioms Crownproof.pow2_secant
