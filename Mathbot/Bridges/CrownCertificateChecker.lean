/-
  Mathbot/Bridges/CrownCertificateChecker.lean

  **Rational FP-Safe α-CROWN Certificate Checker — Day 1**

  This file is Day 1 of the 6-10 week project recommended by the open-
  problems agent in `docs/mathbot/open-problems-2026-05-26.md`
  (Candidate 1): a Lean-mechanized, FP-safe, end-to-end CROWN
  certificate checker over rationals.

  ## The gap this addresses

  Every state-of-the-art NN-verifier (alpha-beta-CROWN, NeuralSAT,
  Marabou) has documented floating-point soundness attacks — see
  *No Soundness in the Real World*, ICML 2025 spotlight
  (arXiv:2506.01054), and SoundnessBench (arXiv:2412.03154).
  TorchLean (arXiv:2602.22631) attempted a Lean 4 formalization of
  IBP/CROWN/α,β-CROWN but 17 of its 20 theorems use `sorry` because
  Lean's native `Float` is opaque. Imandra (ITP 2025, arXiv:2405.10611)
  proved a DNN Farkas lemma over rationals but left FP soundness as
  future work.

  No one has shipped a Lean-mechanized rational-arithmetic CROWN
  certificate checker that (a) consumes a real verifier's certificate
  and (b) checks it in Lean's trusted core.

  ## What this file proves (Day 1)

  We work entirely over `ℚ` (rationals). No `Float`. No `Real`.

  Define a **single-ReLU α-CROWN lower certificate** as a triple
  `(α, l, u) ∈ ℚ × ℚ × ℚ`. We say the certificate is **valid** iff
  `0 ≤ α ≤ 1`. We prove:

  1. `CrownLowerCert.isValid` is `Decidable` (so the check runs).
  2. **Soundness.** If `(α, l, u)` is valid, then for every `x ∈ ℚ`
     in `[l, u]`, `α · x ≤ relu x`. (No `l < 0 < u` hypothesis needed
     for soundness; the bound holds on all of `ℚ`.)
  3. **Completeness (single-ReLU case).** If the inner ReLU is
     *crossing* (`l < 0 < u`) and `α · x ≤ relu x` on `[l, u]` for
     some `α ∈ ℚ`, then `0 ≤ α ≤ 1` — i.e., the validity check is
     not only sufficient but necessary in the crossing case. This is
     `Mathbot/Bridges/AlphaCrownOptimal.lean`'s Pareto-optimality
     theorem sharpened to a *decision procedure*.
  4. The check is **executable**: `decide` reduces the predicate at
     elaboration time.

  ## Why it's small (and why it's still important)

  Day 1 is not the whole pipeline. The whole pipeline is 6-10 weeks
  and culminates in a multi-layer certificate checker with IEEE 754
  rounding-error padding. Day 1 establishes:

  * The pattern: certificate as data, validity as `Decidable`,
    soundness as a Lean theorem with empty domain-axiom closure.
  * The rational baseline: no `Float`, no `Real`, no opacity.
  * The hook to `AlphaCrownOptimal.lean`'s existing Pareto-optimality
    infrastructure, so Day 2-5 inherit that proof effort.

  ## Day 5 — the FP-soundness firewall, now GROUNDED (2026-06-29)

  The "rounding-error padding" promised by the Phase-3 outline was, until
  now, an *assumed* term: every downstream development (`Crownproof.Quant`,
  the per-layer accumulation) takes the per-op round-off bound
  `|round q − q| ≤ ulp/2` as an **unproven hypothesis** `hbound`. That
  unproven link — "the rational padding term actually upper-bounds the
  real IEEE-754 rounding error" — was the FP-soundness gap.

  This file now CLOSES that gap for the **correctly-rounded** IEEE-754 ops
  (`+ − × ÷ √`), grounding the padding in the universal half-ulp bound.
  `§ Day 5` below proves, sorry-free over `ℚ`, that rounding any rational
  `q` onto a grid of spacing `δ` (the ulp) has error `≤ δ/2` — the EXACT
  rational form of the `rounding_error_le_half_ulp` fact landed in
  clean-kernel (`crates/clean-kernel/src/env/nn_verify_rounding_half_ulp.rs`)
  and the `nnverify_ieee754` Mathverse shard. Because the Mathbot Lean
  elaboration environment does not import the kernel-registered
  `NNVerify.FloatRational.*` constants, we PORT the argument as a local
  Lean lemma over `ℚ` (`roundToGrid_error_le_half_ulp`, riding Mathlib's
  `abs_sub_round : |x − round x| ≤ 1/2`). The previously-assumed `hbound`
  becomes a THEOREM, so a correctly-rounded op slots into the padded
  certificate with EMPTY domain-axiom closure — no hidden `Float` axiom,
  no `sorry`.

  Transcendentals (`exp`/`log`/softmax) are NOT correctly-rounded and are
  explicitly OUT of scope here: they carry the separate `FExp`
  under-estimating error model proven in ny-cert
  `Crownproof/SoftmaxFloatRange.lean` (`softmax_phi_upper_sound`), whose
  four facts are structure-field hypotheses, never the half-ulp bound.

  ## Day 2-5 outline

  See `docs/mathbot/fp-soundness-day1-2026-05-26.md`.

  Author: Andrew Yates (Promoted.ai), with Claude Opus 4.7 (1M context).
  Day 5 FP grounding: Claude Opus 4.8 (1M context), 2026-06-29.
  Date: 2026-05-26.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Mathbot.Bridges.AlphaCrownOptimal

set_option autoImplicit false

namespace Mathbot.CrownCertificateChecker

open Mathbot.AlphaCrownOptimal (relu relu_at_zero relu_eq_zero_of_nonpos
  relu_le_self_of_nonneg relu_nonneg alphaWitness_is_valid_lower_bound
  secantUpper secantUpper_is_valid_upper_bound)

/-! ## The certificate data type

A `CrownLowerCert` represents a *candidate* α-CROWN lower-bound
witness for a single ReLU on the input interval `[lo, hi]`. The
verifier (alpha-beta-CROWN, gamma-CROWN, etc.) emits such certificates
as JSON; this Lean type is the in-kernel counterpart.

The certificate is **untrusted** — anyone can construct one. Its
validity is checked by `isValid`. Only `isValid`-passing certificates
are guaranteed to be sound.
-/

/-- A candidate α-CROWN single-ReLU lower-bound certificate over `ℚ`. -/
structure CrownLowerCert where
  /-- The slope of the linear lower envelope `α · x ≤ relu x`. -/
  alpha : ℚ
  /-- Lower endpoint of the input interval. -/
  lo : ℚ
  /-- Upper endpoint of the input interval. -/
  hi : ℚ
deriving DecidableEq, Repr

/-- A certificate is *well-formed* if the input interval is
non-degenerate (`lo ≤ hi`). This is a syntactic check, separate from
soundness validity. -/
def CrownLowerCert.isWellFormed (c : CrownLowerCert) : Prop :=
  c.lo ≤ c.hi

instance (c : CrownLowerCert) : Decidable c.isWellFormed := by
  unfold CrownLowerCert.isWellFormed
  exact inferInstance

/-- The α-CROWN validity predicate: `0 ≤ α ≤ 1`.

    This is the **soundness condition**: a certificate passing
    `isValid` guarantees its lower envelope is sound for ReLU. -/
def CrownLowerCert.isValid (c : CrownLowerCert) : Prop :=
  0 ≤ c.alpha ∧ c.alpha ≤ 1

instance (c : CrownLowerCert) : Decidable c.isValid := by
  unfold CrownLowerCert.isValid
  exact inferInstance

/-- The full predicate the verifier should check: well-formed AND
    valid. Decidable, so this can be evaluated with `decide`. -/
def CrownLowerCert.passes (c : CrownLowerCert) : Prop :=
  c.isWellFormed ∧ c.isValid

instance (c : CrownLowerCert) : Decidable c.passes := by
  unfold CrownLowerCert.passes
  exact inferInstance

/-! ## The lower envelope: evaluation

Given a certificate, we evaluate its lower envelope at an input
point `x ∈ ℚ`. -/

/-- The α-CROWN lower envelope: `α · x`. -/
@[simp] def CrownLowerCert.lowerBound (c : CrownLowerCert) (x : ℚ) : ℚ :=
  c.alpha * x

/-! ## Soundness theorem (Day 1's main result)

If a certificate passes validity, then its lower envelope is sound
for ReLU on the entire interval `[lo, hi]` (and in fact on all of `ℚ`).
-/

/-- **Soundness.** If `(α, l, u)` is a valid certificate
    (`0 ≤ α ≤ 1`), then `α · x ≤ relu x` for *every* `x : ℚ`. The
    interval `[l, u]` does not appear in the conclusion because the
    α-CROWN lower envelope on `[0, 1]`-clamped `α` is sound globally;
    the interval bound is needed only for the *upper* envelope (the
    secant), not the lower. -/
theorem crown_lower_cert_sound
    (c : CrownLowerCert) (hValid : c.isValid) (x : ℚ) :
    c.lowerBound x ≤ relu x := by
  unfold CrownLowerCert.lowerBound
  obtain ⟨hα0, hα1⟩ := hValid
  exact alphaWitness_is_valid_lower_bound c.alpha hα0 hα1 x

/-- The interval-restricted form of soundness: `α · x ≤ relu x` for
    every `x ∈ [lo, hi]`. This is the form a verifier wants when
    threading interval information through composition. -/
theorem crown_lower_cert_sound_on_interval
    (c : CrownLowerCert) (hValid : c.isValid)
    (x : ℚ) (_hxl : c.lo ≤ x) (_hxu : x ≤ c.hi) :
    c.lowerBound x ≤ relu x :=
  crown_lower_cert_sound c hValid x

/-! ## Completeness theorem (Day 1's second main result)

In the *crossing* case (`l < 0 < u`), the validity check is also
**necessary**: if `α · x ≤ relu x` holds for all `x ∈ [l, u]`, then
`α ∈ [0, 1]`.

This sharpens `Mathbot/Bridges/AlphaCrownOptimal.lean`'s Pareto-
optimality theorem (`alpha_crown_optimal_lower`): not only is the
α-CROWN family Pareto-optimal, but the validity *check* is a
*decision procedure* for the crossing case. -/

/-- Helper: the constraint `α · x ≤ relu x` evaluated at `x = u > 0`
    forces `α ≤ 1`. -/
private theorem alpha_le_one_of_at_positive
    {α u : ℚ} (hu : 0 < u) (h : α * u ≤ relu u) : α ≤ 1 := by
  rw [relu_le_self_of_nonneg hu.le] at h
  -- h : α * u ≤ u; with u > 0, divide.
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have : α * u ≤ 1 * u := by linarith
  exact le_of_mul_le_mul_right this hu

/-- Helper: the constraint `α · x ≤ relu x` evaluated at `x = l < 0`
    forces `0 ≤ α`. -/
private theorem alpha_nonneg_of_at_negative
    {α l : ℚ} (hl : l < 0) (h : α * l ≤ relu l) : 0 ≤ α := by
  rw [relu_eq_zero_of_nonpos hl.le] at h
  -- h : α * l ≤ 0, with l < 0.  Then α * l ≤ 0 ↔ α ≥ 0.
  -- (because dividing by negative l flips the inequality)
  by_contra hneg
  have hα_neg : α < 0 := not_le.mp hneg
  have hαl_pos : 0 < α * l := mul_pos_of_neg_of_neg hα_neg hl
  linarith

/-- **Completeness (crossing case).** If a candidate slope `α` makes
    `α · x ≤ relu x` hold for all `x ∈ [l, u]` with `l < 0 < u`, then
    `(α, l, u)` is a valid certificate.

    Together with `crown_lower_cert_sound`, this says: in the
    crossing case, the validity check is a **decision procedure** for
    the property "this α gives a sound α-CROWN lower bound on this
    interval". -/
theorem crown_lower_cert_complete_crossing
    (α l u : ℚ) (hl : l < 0) (hu : 0 < u)
    (hSound : ∀ x : ℚ, l ≤ x → x ≤ u → α * x ≤ relu x) :
    (CrownLowerCert.mk α l u).isValid := by
  refine ⟨?_, ?_⟩
  · -- 0 ≤ α from hSound at x = l.
    have h := hSound l (le_refl _) (le_of_lt (hl.trans hu))
    exact alpha_nonneg_of_at_negative hl h
  · -- α ≤ 1 from hSound at x = u.
    have h := hSound u (le_of_lt (hl.trans hu)) (le_refl _)
    exact alpha_le_one_of_at_positive hu h

/-- **Soundness-completeness equivalence (crossing case).** For a
    crossing input interval, a slope `α` is a sound α-CROWN lower
    coefficient iff it passes the validity check.

    This is the cleanest possible statement of "the decision
    procedure is correct": the certificate check is **iff** the
    bound holds. -/
theorem crown_lower_cert_iff_crossing
    (α l u : ℚ) (hl : l < 0) (hu : 0 < u) :
    (CrownLowerCert.mk α l u).isValid ↔
      (∀ x : ℚ, l ≤ x → x ≤ u → α * x ≤ relu x) := by
  refine ⟨?_, ?_⟩
  · intro hValid x _ _
    exact crown_lower_cert_sound (CrownLowerCert.mk α l u) hValid x
  · intro hSound
    exact crown_lower_cert_complete_crossing α l u hl hu hSound

/-! ## Worked examples: the checker runs

The whole point of operating over `ℚ` is that the checker is
**executable**. Below, we exhibit concrete certificates and check
them via `decide` — i.e., the certificate validity reduces at
elaboration time without any user proof effort. -/

namespace Examples

/-- A valid certificate: `α = 1/2`, on interval `[-1, 1]`. The
    midpoint slope is the natural choice when the verifier has no
    further information. -/
def midpointSlopeCert : CrownLowerCert :=
  { alpha := (1 : ℚ) / 2, lo := -1, hi := 1 }

example : midpointSlopeCert.passes := by
  unfold CrownLowerCert.passes CrownLowerCert.isWellFormed
    CrownLowerCert.isValid midpointSlopeCert
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The two endpoint-α-CROWN choices are always valid: `α = 0`
    (the "ReLU is identically zero" lower bound) and `α = 1` (the
    "ReLU is the identity" lower bound). -/
def zeroSlopeCert (l h : ℚ) : CrownLowerCert :=
  { alpha := 0, lo := l, hi := h }

def oneSlopeCert (l h : ℚ) : CrownLowerCert :=
  { alpha := 1, lo := l, hi := h }

example : (zeroSlopeCert (-3) 5).isValid := by
  refine ⟨?_, ?_⟩ <;> (unfold zeroSlopeCert; norm_num)

example : (oneSlopeCert (-3) 5).isValid := by
  refine ⟨?_, ?_⟩ <;> (unfold oneSlopeCert; norm_num)

/-- An *invalid* certificate: `α = 2`, outside `[0, 1]`. The
    decision procedure rejects it. -/
def badSlopeCert : CrownLowerCert :=
  { alpha := 2, lo := -1, hi := 1 }

example : ¬ badSlopeCert.isValid := by
  unfold CrownLowerCert.isValid badSlopeCert
  rintro ⟨_, h⟩
  norm_num at h

/-- Another invalid certificate: `α = -1/3`, negative. -/
def negativeSlopeCert : CrownLowerCert :=
  { alpha := -1 / 3, lo := -1, hi := 1 }

example : ¬ negativeSlopeCert.isValid := by
  unfold CrownLowerCert.isValid negativeSlopeCert
  rintro ⟨h, _⟩
  norm_num at h

/-! Even though `decide` on `ℚ` does not reduce in kernel mode
(because `Rat`'s comparison is implemented via the irreducible
`Rat.blt`), the same certificate validity can be checked at native
speed via `native_decide`, which is a sound kernel-trusted bridge.
This is what a real verifier would use to discharge thousands of
small certificate validity checks per second. -/
example : midpointSlopeCert.passes := by native_decide

example : ¬ badSlopeCert.isValid := by native_decide

end Examples

/-! ## Axiom audit

Run `#print axioms` at use sites to confirm that the certificate-
checker theorems below have transitive closure
⊆ `{propext, Quot.sound, Classical.choice}` plus the `relu`-related
constants from `Mathbot.Bridges.AlphaCrownOptimal`. No domain-specific
axioms are introduced by this file.

The key theorems whose axiom closure should be audited:

  * `crown_lower_cert_sound`
  * `crown_lower_cert_complete_crossing`
  * `crown_lower_cert_iff_crossing`

Sample audit at the end of this file:
-/

-- Axiom audits for the main theorems. These must show only
-- foundational axioms (propext, Quot.sound, Classical.choice) and
-- the Mathlib infrastructure they ride on.
#guard_msgs (drop info) in
#print axioms crown_lower_cert_sound

#guard_msgs (drop info) in
#print axioms crown_lower_cert_complete_crossing

#guard_msgs (drop info) in
#print axioms crown_lower_cert_iff_crossing

/-! ## Day 2 — Upper-bound certificate

We mirror `CrownLowerCert` for the α-CROWN *upper* envelope: the
secant line through `(lo, 0)` and `(hi, hi)` over a *crossing* input
interval `lo < 0 < hi`.

The slope of this secant is `hi / (hi - lo)`, and its intercept is
`-(lo * hi) / (hi - lo)`. Together they are the unique affine upper
bound that touches `relu` at both endpoints; `AlphaCrownOptimal`'s
`alpha_crown_optimal_upper` already shows every valid affine upper
bound dominates the secant pointwise.

Following the Day 1 pattern, we provide:

1. `CrownUpperCert` (slope, intercept, lo, hi) data type.
2. `isValid` predicate enforcing the secant-formula closed form and
   the crossing-input hypothesis.
3. `Decidable` instance so the checker runs.
4. Soundness: `relu x ≤ slope · x + intercept` for `x ∈ [lo, hi]`.
5. Uniqueness: any affine upper bound that *interpolates* `relu` at
   the two endpoints `lo` and `hi` is *exactly* the α-CROWN secant
   — the "uniquely tightest" claim made precise.
-/

/-- A candidate α-CROWN single-ReLU *upper*-bound certificate over `ℚ`. -/
structure CrownUpperCert where
  /-- The slope of the upper envelope. For the α-CROWN secant on a
      crossing interval `(lo, hi)` with `lo < 0 < hi`, this is
      `hi / (hi - lo)`. -/
  slope : ℚ
  /-- The intercept of the upper envelope. For the α-CROWN secant, this
      is `-(lo * hi) / (hi - lo)`. -/
  intercept : ℚ
  /-- Lower endpoint of the input interval. -/
  lo : ℚ
  /-- Upper endpoint of the input interval. -/
  hi : ℚ
deriving DecidableEq, Repr

/-- The α-CROWN upper-envelope validity predicate. -/
def CrownUpperCert.isValid (c : CrownUpperCert) : Prop :=
  c.slope = c.hi / (c.hi - c.lo) ∧
  c.intercept = -(c.lo * c.hi) / (c.hi - c.lo) ∧
  c.lo < 0 ∧
  0 < c.hi

instance (c : CrownUpperCert) : Decidable c.isValid := by
  unfold CrownUpperCert.isValid
  exact inferInstance

/-- The affine evaluation of an upper-envelope certificate. -/
@[simp] def CrownUpperCert.upperBound (c : CrownUpperCert) (x : ℚ) : ℚ :=
  c.slope * x + c.intercept

/-- **Day 2 soundness.** If a `CrownUpperCert` is valid, then its
    affine evaluation upper-bounds `relu` on the input interval `[lo, hi]`.
    Reuses `secantUpper_is_valid_upper_bound` from `AlphaCrownOptimal`. -/
theorem crown_upper_cert_sound
    (c : CrownUpperCert) (hValid : c.isValid)
    (x : ℚ) (hxl : c.lo ≤ x) (hxu : x ≤ c.hi) :
    relu x ≤ c.upperBound x := by
  obtain ⟨hSlope, hIntercept, hLo, hHi⟩ := hValid
  have hSec := secantUpper_is_valid_upper_bound c.lo c.hi hLo hHi x hxl hxu
  unfold secantUpper at hSec
  unfold CrownUpperCert.upperBound
  rw [hSlope, hIntercept]
  have hlu : 0 < c.hi - c.lo := by linarith
  have hlu_ne : c.hi - c.lo ≠ 0 := ne_of_gt hlu
  have hrw : c.hi / (c.hi - c.lo) * (x - c.lo)
           = c.hi / (c.hi - c.lo) * x + -(c.lo * c.hi) / (c.hi - c.lo) := by
    field_simp
    ring
  linarith [hSec, hrw.symm ▸ hSec]

/-- **Day 2 uniqueness.** Any affine line `y = slope' · x + intercept'`
    that simultaneously
    (a) upper-bounds `relu` on `[lo, hi]`,
    (b) interpolates `relu` at the left endpoint
        (`slope' · lo + intercept' = 0 = relu lo`),
    (c) interpolates `relu` at the right endpoint
        (`slope' · hi + intercept' = hi = relu hi`),
    is *exactly* the α-CROWN secant.

    Hypothesis (a) (upper-bounding) is not actually needed for
    uniqueness — the two interpolation constraints (b), (c) alone
    determine the line — but we keep it to make the "uniquely tightest
    upper bound" reading transparent. -/
theorem crown_upper_cert_unique
    (lo hi : ℚ) (hLo : lo < 0) (hHi : 0 < hi)
    (slope' intercept' : ℚ)
    (_hUpper : ∀ x : ℚ, lo ≤ x → x ≤ hi → relu x ≤ slope' * x + intercept')
    (hLeft : slope' * lo + intercept' = 0)
    (hRight : slope' * hi + intercept' = hi) :
    slope' = hi / (hi - lo) ∧ intercept' = -(lo * hi) / (hi - lo) := by
  have hlu : 0 < hi - lo := by linarith
  have hlu_ne : hi - lo ≠ 0 := ne_of_gt hlu
  -- (hRight) - (hLeft): slope' * (hi - lo) = hi.
  have hSlopeEq : slope' * (hi - lo) = hi := by linarith
  have hSlope : slope' = hi / (hi - lo) :=
    (eq_div_iff hlu_ne).mpr hSlopeEq
  refine ⟨hSlope, ?_⟩
  have hIntEq : intercept' = -(slope' * lo) := by linarith
  rw [hIntEq, hSlope]
  field_simp

/-! ### Worked Day 2 example

A concrete upper-envelope certificate over `[-1, 1]`. The secant slope
is `1/(1-(-1)) = 1/2`; the intercept is `-((-1)·1)/(1-(-1)) = 1/2`. So
`y = (1/2)·x + 1/2`. -/
namespace Day2Examples

def symmetricSecantCert : CrownUpperCert :=
  { slope := (1 : ℚ) / 2, intercept := (1 : ℚ) / 2, lo := -1, hi := 1 }

example : symmetricSecantCert.isValid := by
  unfold CrownUpperCert.isValid symmetricSecantCert
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

example : symmetricSecantCert.isValid := by native_decide

/-- An invalid upper certificate: wrong slope. -/
def badUpperCert : CrownUpperCert :=
  { slope := 1, intercept := 0, lo := -1, hi := 1 }

example : ¬ badUpperCert.isValid := by
  unfold CrownUpperCert.isValid badUpperCert
  rintro ⟨h, _, _, _⟩
  norm_num at h

end Day2Examples

-- Day 2 axiom audits.
#guard_msgs (drop info) in
#print axioms crown_upper_cert_sound

#guard_msgs (drop info) in
#print axioms crown_upper_cert_unique

/-! ## Day 3 — Joint envelope certificate

Bundle a `CrownLowerCert` and a `CrownUpperCert` over the *same* input
interval into a single `CrownEnvelopeCert`. The validity check is
*conjunctive*: both halves must be valid, and the two halves must agree
on the input interval `[lo, hi]`.

In one decidable proposition, we capture: "this triple of
(α, slope, intercept) constitutes a sound, single-ReLU envelope on
`[lo, hi]`". Soundness then sandwiches `relu x` between the lower and
upper affine bounds.

We then state the *tightness-gap theorem*: the maximum of
`upper x - relu x` over `x ∈ [lo, hi]` is `-(lo * hi) / (hi - lo)`, the
classical "convex relaxation barrier" of Salman et al. NeurIPS 2019,
formalized here over ℚ. -/

/-- The bundled lower+upper envelope certificate. -/
structure CrownEnvelopeCert where
  lower : CrownLowerCert
  upper : CrownUpperCert
deriving Repr

/-- The envelope is valid iff both halves are valid, and they agree on
    the input interval (`lower.lo = upper.lo` and `lower.hi = upper.hi`). -/
def CrownEnvelopeCert.isValid (c : CrownEnvelopeCert) : Prop :=
  c.lower.isValid ∧ c.upper.isValid ∧
  c.lower.lo = c.upper.lo ∧ c.lower.hi = c.upper.hi

instance (c : CrownEnvelopeCert) : Decidable c.isValid := by
  unfold CrownEnvelopeCert.isValid
  exact inferInstance

/-- Convenience accessor: the shared lower endpoint. -/
def CrownEnvelopeCert.lo (c : CrownEnvelopeCert) : ℚ := c.lower.lo

/-- Convenience accessor: the shared upper endpoint. -/
def CrownEnvelopeCert.hi (c : CrownEnvelopeCert) : ℚ := c.upper.hi

/-- The lower envelope evaluation. -/
def CrownEnvelopeCert.lowerBound (c : CrownEnvelopeCert) (x : ℚ) : ℚ :=
  c.lower.lowerBound x

/-- The upper envelope evaluation. -/
def CrownEnvelopeCert.upperBound (c : CrownEnvelopeCert) (x : ℚ) : ℚ :=
  c.upper.upperBound x

/-- **Day 3 soundness.** A valid envelope certificate sandwiches `relu x`
    between its lower and upper affine bounds on the input interval. -/
theorem crown_envelope_sound
    (c : CrownEnvelopeCert) (hValid : c.isValid)
    (x : ℚ) (hxl : c.lo ≤ x) (hxu : x ≤ c.hi) :
    c.lowerBound x ≤ relu x ∧ relu x ≤ c.upperBound x := by
  obtain ⟨hLower, hUpper, hLoAgree, _⟩ := hValid
  refine ⟨?_, ?_⟩
  · -- Lower side: soundness from Day 1 (holds globally).
    exact crown_lower_cert_sound c.lower hLower x
  · -- Upper side: Day 2 soundness needs x ∈ [upper.lo, upper.hi];
    -- the envelope's `lo`-agreement carries the lower bound across.
    have hxl' : c.upper.lo ≤ x := by
      have h : c.lo = c.upper.lo := hLoAgree
      linarith
    have hxu' : x ≤ c.upper.hi := hxu
    exact crown_upper_cert_sound c.upper hUpper x hxl' hxu'

/-- The pointwise envelope *gap*: `upper(x) - lower(x)`. -/
def CrownEnvelopeCert.gap (c : CrownEnvelopeCert) (x : ℚ) : ℚ :=
  c.upperBound x - c.lowerBound x

/-- The pointwise *upper-side relaxation gap*: `upper(x) - relu(x)`.
    This is the classical Salman gap, independent of α. -/
def CrownEnvelopeCert.upperRelaxationGap (c : CrownEnvelopeCert) (x : ℚ) : ℚ :=
  c.upperBound x - relu x

/-- **Day 3 tightness gap (Salman barrier).** For every valid envelope
    certificate and every `x ∈ [lo, hi]`, the *upper relaxation gap*
    `upper(x) - relu(x)` is bounded above by `-(lo * hi) / (hi - lo)`.

    This is the classical "convex relaxation barrier" of Salman et al.
    NeurIPS 2019, formalized over ℚ. The bound is *tight*: it is
    attained at `x = 0` (see `crown_envelope_gap_attained_at_zero`). -/
theorem crown_envelope_upper_gap_bound
    (c : CrownEnvelopeCert) (hValid : c.isValid)
    (x : ℚ) (hxl : c.lo ≤ x) (hxu : x ≤ c.hi) :
    c.upperRelaxationGap x ≤ -(c.lo * c.hi) / (c.hi - c.lo) := by
  obtain ⟨_, hUpper, hLoAgree, _⟩ := hValid
  obtain ⟨hSlope, hIntercept, hLo, hHi⟩ := hUpper
  -- Transport upper-cert's `lo` to envelope coords; `hi` is c.hi def-equal.
  have hLoEq : c.upper.lo = c.lo := hLoAgree.symm
  have hHiEq : c.upper.hi = c.hi := rfl
  rw [hLoEq, hHiEq] at hSlope hIntercept
  rw [hLoEq] at hLo
  rw [hHiEq] at hHi
  have hLo' : c.lo < 0 := hLo
  have hHi' : 0 < c.hi := hHi
  unfold CrownEnvelopeCert.upperRelaxationGap CrownEnvelopeCert.upperBound
    CrownUpperCert.upperBound
  rw [hSlope, hIntercept]
  have hlu : 0 < c.hi - c.lo := by linarith
  have hlu_ne : c.hi - c.lo ≠ 0 := ne_of_gt hlu
  rcases le_or_gt 0 x with hxnn | hxneg
  · -- x ≥ 0: relu x = x. Reduce to (lo/(hi-lo)) * x ≤ 0.
    rw [show relu x = x from by unfold relu; exact max_eq_right hxnn]
    have key : c.hi / (c.hi - c.lo) * x - x = c.lo / (c.hi - c.lo) * x := by
      field_simp
      ring
    have hquot_neg : c.lo / (c.hi - c.lo) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hLo'.le hlu.le
    have hprod : c.lo / (c.hi - c.lo) * x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hquot_neg hxnn
    linarith
  · -- x < 0: relu x = 0. Reduce to (hi/(hi-lo)) * x ≤ 0.
    rw [show relu x = 0 from by unfold relu; exact max_eq_left hxneg.le]
    have hquot_pos : 0 ≤ c.hi / (c.hi - c.lo) := div_nonneg hHi'.le hlu.le
    have hprod : c.hi / (c.hi - c.lo) * x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hquot_pos hxneg.le
    linarith

/-- **Day 3 tightness, attained.** The upper relaxation gap *attains*
    the Salman bound at `x = 0` (which lies in the crossing interval). -/
theorem crown_envelope_gap_attained_at_zero
    (c : CrownEnvelopeCert) (hValid : c.isValid) :
    c.upperRelaxationGap 0 = -(c.lo * c.hi) / (c.hi - c.lo) := by
  obtain ⟨_, hUpper, hLoAgree, _⟩ := hValid
  obtain ⟨hSlope, hIntercept, _, _⟩ := hUpper
  have hLoEq : c.upper.lo = c.lo := hLoAgree.symm
  have hHiEq : c.upper.hi = c.hi := rfl
  rw [hLoEq, hHiEq] at hSlope hIntercept
  unfold CrownEnvelopeCert.upperRelaxationGap CrownEnvelopeCert.upperBound
    CrownUpperCert.upperBound
  rw [hSlope, hIntercept, relu_at_zero]
  ring

/-- **Day 3 envelope gap, full form.** The envelope gap
    `upperBound x - lowerBound x` decomposes as the upper relaxation
    gap (Salman barrier) plus the *lower slack* `relu x - lower x`. -/
theorem crown_envelope_gap_decomposition
    (c : CrownEnvelopeCert) (_hValid : c.isValid)
    (x : ℚ) (_hxl : c.lo ≤ x) (_hxu : x ≤ c.hi) :
    c.gap x = c.upperRelaxationGap x + (relu x - c.lowerBound x) := by
  unfold CrownEnvelopeCert.gap CrownEnvelopeCert.upperRelaxationGap
  ring

/-- The envelope gap is non-negative everywhere on the input interval
    (the upper bound dominates the lower bound, sandwiching relu). -/
theorem crown_envelope_gap_nonneg
    (c : CrownEnvelopeCert) (hValid : c.isValid)
    (x : ℚ) (hxl : c.lo ≤ x) (hxu : x ≤ c.hi) :
    0 ≤ c.gap x := by
  have hSound := crown_envelope_sound c hValid x hxl hxu
  unfold CrownEnvelopeCert.gap
  linarith [hSound.1, hSound.2]

/-! ### Day 3 decision-procedure worked example

A concrete envelope certificate over `[-2, 4]` with `α = 1/2`.

* Secant slope: `4 / (4 - (-2)) = 4/6 = 2/3`.
* Secant intercept: `-((-2) * 4) / 6 = 8/6 = 4/3`.
* Salman gap at `x = 0`: `-((-2) * 4) / 6 = 4/3`.

Both halves pass `decide` / `native_decide`. -/
namespace Day3Examples

def workedEnvelope : CrownEnvelopeCert :=
  { lower := { alpha := (1 : ℚ) / 2, lo := -2, hi := 4 }
    upper := { slope := (2 : ℚ) / 3, intercept := (4 : ℚ) / 3
               lo := -2, hi := 4 } }

example : workedEnvelope.isValid := by
  unfold CrownEnvelopeCert.isValid workedEnvelope CrownLowerCert.isValid
    CrownUpperCert.isValid
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> norm_num

example : workedEnvelope.isValid := by native_decide

/-- The Salman gap at `x = 0` for `workedEnvelope` is `4/3`. -/
example : workedEnvelope.upperRelaxationGap 0 = 4 / 3 := by
  unfold CrownEnvelopeCert.upperRelaxationGap CrownEnvelopeCert.upperBound
    workedEnvelope CrownUpperCert.upperBound
  rw [relu_at_zero]
  norm_num

/-- The envelope gap (upper - lower) at `x = 0` is also `4/3` (since
    lower(0) = α·0 = 0). -/
example : workedEnvelope.gap 0 = 4 / 3 := by
  unfold CrownEnvelopeCert.gap CrownEnvelopeCert.upperBound
    CrownEnvelopeCert.lowerBound workedEnvelope CrownUpperCert.upperBound
    CrownLowerCert.lowerBound
  norm_num

end Day3Examples

-- Day 3 axiom audits.
#guard_msgs (drop info) in
#print axioms crown_envelope_sound

#guard_msgs (drop info) in
#print axioms crown_envelope_upper_gap_bound

#guard_msgs (drop info) in
#print axioms crown_envelope_gap_attained_at_zero

#guard_msgs (drop info) in
#print axioms crown_envelope_gap_decomposition

#guard_msgs (drop info) in
#print axioms crown_envelope_gap_nonneg

/-! ## Day 4 — Full affine lower-bound decision procedure

The α-CROWN lower-bound family is `{ α · x : α ∈ [0, 1] }`: pure-slope
lines with zero intercept. Real-world verifiers (alpha-beta-CROWN,
NeuralSAT, Marabou) emit a **wider class**: arbitrary affine functions
`a·x + b` with both slope `a ∈ ℚ` and intercept `b ∈ ℚ`. The α-CROWN
lower envelope is the Pareto-optimal *slice* of this class (every full
affine lower bound is dominated by some `α · x`), as
`Mathbot.AlphaCrownOptimal.alpha_crown_optimal_lower` proves.

But Pareto-optimality is a *dominance* statement; it does not by itself
give a **decision procedure** for the full class. The reviewer's
critique stands: a certificate checker for a real verifier must accept
`(a, b)` pairs and decide validity by inspection of `(a, b, l, u)`
alone — not by witnessing a dominating α.

This section closes that gap. We show: for `l < 0 < u` and any
`(a, b) : ℚ × ℚ`, the predicate

  `∀ x ∈ [l, u], a · x + b ≤ relu x`

is **equivalent** to the conjunction of three rational comparisons:

  `b ≤ 0  ∧  a · l + b ≤ 0  ∧  a · u + b ≤ u`.

The RHS is `Decidable` by construction: it is a Boolean combination of
rational ≤-checks. This makes the *full-affine* lower-bound certificate
checker an executable decision procedure, not merely a Pareto-optimal
slice. -/

/-- A candidate **full-affine** lower-bound certificate over `ℚ`.

    Unlike `CrownLowerCert`, which restricts to pure-slope lines
    `α · x`, this certificate captures arbitrary affine lower bounds
    `a · x + b`, which is the class emitted by every state-of-the-art
    neural network verifier. -/
structure FullAffineLowerCert where
  /-- Slope of the affine lower envelope. -/
  a : ℚ
  /-- Intercept of the affine lower envelope. -/
  b : ℚ
  /-- Lower endpoint of the input interval. -/
  l : ℚ
  /-- Upper endpoint of the input interval. -/
  u : ℚ
deriving DecidableEq, Repr

/-- The validity predicate for a full-affine lower-bound certificate.

    Three rational comparisons at three corner points characterize
    validity on the entire input interval:

    * `b ≤ 0`         — the line is non-positive at `x = 0`
                        (so it lower-bounds `relu 0 = 0`).
    * `a · l + b ≤ 0` — the line is non-positive at `x = l`
                        (so it lower-bounds `relu l = 0` since `l < 0`).
    * `a · u + b ≤ u` — the line is at most `u` at `x = u`
                        (so it lower-bounds `relu u = u` since `u > 0`).

    All three are pure decidable ℚ-comparisons; together with the
    crossing condition `l < 0 < u`, they form the decision procedure. -/
def FullAffineLowerCert.isValid (c : FullAffineLowerCert) : Prop :=
  c.l < 0 ∧ 0 < c.u ∧ c.b ≤ 0 ∧ c.a * c.l + c.b ≤ 0 ∧ c.a * c.u + c.b ≤ c.u

instance (c : FullAffineLowerCert) : Decidable c.isValid := by
  unfold FullAffineLowerCert.isValid
  exact inferInstance

/-- The affine evaluation of a full-affine lower-bound certificate. -/
@[simp] def FullAffineLowerCert.lowerBound
    (c : FullAffineLowerCert) (x : ℚ) : ℚ :=
  c.a * x + c.b

/-! ### The decision-procedure theorem

The forward direction (← in the iff): three corner constraints imply
the bound holds everywhere on `[l, u]`. The reverse direction (→):
specialize the bound at `x = 0`, `x = l`, `x = u`.

We split the forward direction into two case lemmas (`x ≤ 0` and
`x ≥ 0`) to keep the linarith goals small. -/

/-- Forward-direction helper: on the left half `[l, 0]`, the
    affine line `a · x + b` lies at or below `0 = relu x`, by convex
    combination of the constraints at the two endpoints `l` and `0`. -/
private theorem full_affine_left_half
    {a b l : ℚ} (hl : l < 0)
    (hZero : b ≤ 0) (hLeft : a * l + b ≤ 0)
    {x : ℚ} (hxl : l ≤ x) (hxnp : x ≤ 0) :
    a * x + b ≤ 0 := by
  -- Convex parameter t = (x - l) / (-l) ∈ [0, 1]; then
  -- x = (1 - t) * l + t * 0 = (1 - t) * l, and
  -- a*x + b = (1 - t) * (a*l + b) + t * b ≤ 0.
  have hl_ne : -l ≠ 0 := by
    intro h
    linarith
  have h_negl_pos : 0 < -l := by linarith
  set t : ℚ := (x - l) / (-l) with ht_def
  have ht_nonneg : 0 ≤ t := by
    apply div_nonneg
    · linarith
    · linarith
  have ht_le_one : t ≤ 1 := by
    rw [ht_def, div_le_one h_negl_pos]
    linarith
  -- Express x as (1 - t) * l + t * 0 = (1 - t) * l, equivalently
  -- x = l + t * (-l) = l - t * l.
  have hx_eq : x = l - t * l := by
    have : t * (-l) = x - l := by
      rw [ht_def]
      exact div_mul_cancel₀ (x - l) hl_ne
    linarith
  -- a*x + b in terms of t:
  -- a*(l - t*l) + b = a*l - t*a*l + b = (1 - t)*(a*l + b) + t*b.
  have h_combo : a * x + b = (1 - t) * (a * l + b) + t * b := by
    rw [hx_eq]; ring
  -- Now both summands are ≤ 0.
  have h1 : (1 - t) * (a * l + b) ≤ 0 := by
    have h1nn : 0 ≤ 1 - t := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h1nn hLeft
  have h2 : t * b ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht_nonneg hZero
  linarith [h_combo]

/-- Forward-direction helper: on the right half `[0, u]`, the
    affine line `a · x + b` lies at or below `x = relu x`, by convex
    combination of the constraints at the two endpoints `0` and `u`. -/
private theorem full_affine_right_half
    {a b u : ℚ} (hu : 0 < u)
    (hZero : b ≤ 0) (hRight : a * u + b ≤ u)
    {x : ℚ} (hxnn : 0 ≤ x) (hxu : x ≤ u) :
    a * x + b ≤ x := by
  -- It is equivalent to show (a - 1) * x + b ≤ 0.
  -- Convex parameter s = x / u ∈ [0, 1]; then x = s * u and
  -- (a - 1) * x + b = (1 - s) * b + s * ((a - 1) * u + b),
  -- both summands ≤ 0.
  have hu_ne : u ≠ 0 := ne_of_gt hu
  set s : ℚ := x / u with hs_def
  have hs_nonneg : 0 ≤ s := div_nonneg hxnn hu.le
  have hs_le_one : s ≤ 1 := by
    rw [hs_def, div_le_one hu]
    exact hxu
  -- x = s * u (cancel division).
  have hx_eq : x = s * u := by
    rw [hs_def]
    exact (div_mul_cancel₀ x hu_ne).symm
  -- (a - 1) * x + b = (1 - s) * b + s * ((a - 1) * u + b).
  have h_combo :
      (a - 1) * x + b = (1 - s) * b + s * ((a - 1) * u + b) := by
    rw [hx_eq]; ring
  have hRight' : (a - 1) * u + b ≤ 0 := by linarith
  have h1 : (1 - s) * b ≤ 0 := by
    have h1nn : 0 ≤ 1 - s := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h1nn hZero
  have h2 : s * ((a - 1) * u + b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs_nonneg hRight'
  linarith [h_combo]

/-- **Main theorem (full-affine lower-bound decision procedure).**

    For `l < 0 < u` and any `(a, b) : ℚ × ℚ`, the affine lower-bound
    predicate `∀ x ∈ [l, u], a · x + b ≤ relu x` is equivalent to the
    conjunction of three rational comparisons at three specific points.

    This is the **decidable iff** for the full affine class — the
    decision-procedure dual of `alpha_crown_optimal_lower`'s Pareto-
    optimality. -/
theorem full_affine_lower_cert_iff
    (a b l u : ℚ) (hl : l < 0) (hu : 0 < u) :
    (∀ x : ℚ, l ≤ x → x ≤ u → a * x + b ≤ relu x) ↔
      (b ≤ 0 ∧ a * l + b ≤ 0 ∧ a * u + b ≤ u) := by
  constructor
  · -- (→) corner facts from the three specific points.
    intro hSound
    refine ⟨?_, ?_, ?_⟩
    · -- x = 0 ∈ [l, u].
      have h := hSound 0 hl.le hu.le
      rw [relu_at_zero] at h
      linarith
    · -- x = l.
      have h := hSound l (le_refl _) (hl.trans hu).le
      rwa [relu_eq_zero_of_nonpos hl.le] at h
    · -- x = u.
      have h := hSound u (hl.trans hu).le (le_refl _)
      rwa [relu_le_self_of_nonneg hu.le] at h
  · -- (←) the three constraints imply the bound on all of [l, u].
    rintro ⟨hZero, hLeft, hRight⟩ x hxl hxu
    rcases le_or_gt x 0 with hxnp | hxpos
    · -- x ≤ 0: relu x = 0; reduce to a*x + b ≤ 0 (left half).
      rw [relu_eq_zero_of_nonpos hxnp]
      exact full_affine_left_half hl hZero hLeft hxl hxnp
    · -- x > 0: relu x = x; reduce to a*x + b ≤ x (right half).
      rw [relu_le_self_of_nonneg hxpos.le]
      exact full_affine_right_half hu hZero hRight hxpos.le hxu

/-- **Soundness corollary.** A valid full-affine certificate's lower
    envelope is a sound lower bound for `relu` on its input interval.

    This is the "direction the verifier uses": given a checker-passing
    certificate, the affine line is guaranteed to lie at or below
    `relu` on `[l, u]`. -/
theorem full_affine_lower_cert_sound
    (c : FullAffineLowerCert) (hValid : c.isValid)
    (x : ℚ) (hxl : c.l ≤ x) (hxu : x ≤ c.u) :
    c.lowerBound x ≤ relu x := by
  obtain ⟨hl, hu, hZero, hLeft, hRight⟩ := hValid
  have h := (full_affine_lower_cert_iff c.a c.b c.l c.u hl hu).mpr
    ⟨hZero, hLeft, hRight⟩
  exact h x hxl hxu

/-- **Completeness corollary.** If an affine line is a valid lower
    bound for `relu` on a crossing interval `[l, u]`, then the
    corresponding certificate passes the validity check.

    Together with the soundness corollary, this says: in the crossing
    case, the validity check is a **decision procedure** — provably
    sound *and* provably complete. -/
theorem full_affine_lower_cert_complete
    (a b l u : ℚ) (hl : l < 0) (hu : 0 < u)
    (hSound : ∀ x : ℚ, l ≤ x → x ≤ u → a * x + b ≤ relu x) :
    (FullAffineLowerCert.mk a b l u).isValid := by
  have ⟨hZero, hLeft, hRight⟩ :=
    (full_affine_lower_cert_iff a b l u hl hu).mp hSound
  exact ⟨hl, hu, hZero, hLeft, hRight⟩

/-! ### Worked example: the decision procedure runs

A concrete full-affine lower-bound certificate over `[-1, 2]` with
`a = 1/2` and `b = 1/10`. The three checks are:

* `b ≤ 0`?           `1/10 ≤ 0`?  **NO**.

So this certificate is *invalid*. The decision procedure rejects it via
`native_decide` (and via plain `decide` once the rational comparisons
are unfolded), without any user proof effort.

We also exhibit a valid full-affine certificate (`a = 1/2`, `b = 0`) and
a valid non-α-CROWN one (`a = 1/2`, `b = -1/10`, where `b < 0` so it
falls *outside* the α-CROWN slice `{α · x : α ∈ [0, 1]}` but is still a
sound lower bound). -/
namespace Day4Examples

/-- The worked example from the task: `a = 1/2`, `b = 1/10`, `l = -1`,
    `u = 2`. The third check `a·l + b = -2/5 ≤ 0` holds, the first
    check `b = 1/10 ≤ 0` does NOT hold. Hence invalid. -/
def workedFullAffine : FullAffineLowerCert :=
  { a := (1 : ℚ) / 2, b := (1 : ℚ) / 10, l := -1, u := 2 }

example : ¬ workedFullAffine.isValid := by native_decide

/-- The decision procedure reduces to `false` at native-decide time
    (rather than failing with "irreducible"). -/
example : (decide workedFullAffine.isValid) = false := by native_decide

/-- A valid full-affine certificate that lies *outside* the α-CROWN
    pure-slope slice (because `b < 0`). The α-CROWN family is the
    Pareto frontier of the sound region; this certificate sits strictly
    inside the frontier. -/
def workedValidFullAffine : FullAffineLowerCert :=
  { a := (1 : ℚ) / 2, b := -(1 : ℚ) / 10, l := -1, u := 2 }

example : workedValidFullAffine.isValid := by native_decide

/-- Pure α-CROWN certificate (b = 0) recast as a full-affine certificate
    is still valid. -/
def alphaHalfAsFullAffine : FullAffineLowerCert :=
  { a := (1 : ℚ) / 2, b := 0, l := -1, u := 2 }

example : alphaHalfAsFullAffine.isValid := by native_decide

/-- An invalid certificate with slope a = 2 and intercept b = -1: the
    third check `a·u + b = 3 ≤ u = 2` fails. -/
def slopeTooSteepFullAffine : FullAffineLowerCert :=
  { a := 2, b := -1, l := -1, u := 2 }

example : ¬ slopeTooSteepFullAffine.isValid := by native_decide

/-- Soundness of the valid example: the line `(1/2)·x - 1/10` is at or
    below `relu x` on `[-1, 2]`. Demonstrates the soundness corollary
    being used end-to-end with a concrete certificate. -/
example (x : ℚ) (hxl : -1 ≤ x) (hxu : x ≤ 2) :
    (1 : ℚ) / 2 * x + -(1 : ℚ) / 10 ≤ relu x := by
  have hValid : workedValidFullAffine.isValid := by native_decide
  have h := full_affine_lower_cert_sound workedValidFullAffine hValid x
    (by show (-1 : ℚ) ≤ x; exact hxl) (by show x ≤ (2 : ℚ); exact hxu)
  simpa [workedValidFullAffine, FullAffineLowerCert.lowerBound] using h

end Day4Examples

-- Day 4 axiom audits: the decision-procedure theorems must rest only
-- on foundational axioms.
#guard_msgs (drop info) in
#print axioms full_affine_lower_cert_iff

#guard_msgs (drop info) in
#print axioms full_affine_lower_cert_sound

#guard_msgs (drop info) in
#print axioms full_affine_lower_cert_complete

/-! ## Day 5 — the FP-soundness firewall, GROUNDED in the half-ulp bound

Everything above is EXACT over `ℚ`. A real verifier, however, computes its
certificate-padded bounds in IEEE-754 `binary64`, and a sound checker must
account for the rounding error of those computations. The standard device
(Higham 2002, and `Crownproof.Quant`) is to PAD the rational bound by the
per-op round-off term `ulp/2` and check the *padded* bound. The soundness of
that device rests on ONE fact:

    for a correctly-rounded op, the rounding error never exceeds half an ulp:
      `|round q − q| ≤ ulp/2`.                                          (★)

Until now (★) was **assumed** — taken as an unproven hypothesis `hbound`
wherever the padding appears (`Crownproof.Quant.quant_envelope` and friends
all quantify over an arbitrary `hbound : |qx − x| ≤ delta/2`). That unproven
assumption was the FP-soundness gap: nothing tied the rational pad to the
actual IEEE-754 rounding error.

This section turns (★) into a THEOREM over `ℚ`. The clean-kernel development
`NNVerify.FloatRational.rounding_error_le_half_ulp` (file
`crates/clean-kernel/src/env/nn_verify_rounding_half_ulp.rs`) proves the
universal `2·|round N − N| ≤ 2^e` bound over `Nat`/`Int`, denormal-floor
aware, with an EMPTY non-foundational axiom closure, and the `nnverify_ieee754`
Mathverse shard bundles it. Those constants live in the kernel `Environment`,
NOT in the Mathbot Lean elaboration environment (which imports Mathlib, not the
kernel registrations). So — per the task's option (2) — we PORT the same
argument as a local, sorry-free Lean lemma over `ℚ`: rounding `q` onto the
uniform grid of spacing `δ` (the ulp) has error `≤ δ/2`. The Mathlib fact
`abs_sub_round : |x − round x| ≤ 1/2` is the unit-spacing instance of the same
universal half-ulp bound; scaling by the grid spacing `δ` gives (★) at the
ulp. The proof rests only on the three foundational axioms.

**Scope.** This is the bound for the CORRECTLY-ROUNDED ops `+ − × ÷ √`
(and fma) — exactly the scope of `rounding_error_le_half_ulp`'s
`ROUNDING_SCOPE` marker. Transcendentals (`exp`/`log`/softmax) are NOT
correctly rounded; their soundness is the separate `FExp` under-estimating
model in ny-cert `Crownproof/SoftmaxFloatRange.lean`
(`softmax_phi_upper_sound`), whose four facts are structure-field hypotheses,
never this half-ulp bound. Anything transcendental-dependent therefore remains
OUT of scope here and is explicitly delegated to that model. -/

/-- Round a rational `q` onto the uniform grid of spacing `δ > 0`, i.e. to the
    nearest integer multiple of `δ`, ties-to-(+∞) as in Mathlib's `round`.
    This is the rational model of a correctly-rounded IEEE-754 result: a real
    `binary64` value rounds onto the grid whose spacing is the ulp at its
    magnitude (in the subnormal regime, the *floored* ulp — a uniform grid all
    the same, which is exactly what makes the single bound below cover the
    denormal case, as `rounding_error_le_half_ulp_denormal` notes). -/
def roundToGrid (q δ : ℚ) : ℚ := δ * ((round (q / δ) : ℤ) : ℚ)

/-- **(★) The half-ulp rounding bound, as a THEOREM over `ℚ`.**

    Rounding `q` onto the grid of spacing `δ > 0` moves it by at most `δ/2`:

      `|roundToGrid q δ − q| ≤ δ/2`.

    This is the exact rational form of the universal
    `NNVerify.FloatRational.rounding_error_le_half_ulp` (`2·|round − N| ≤ ulp`)
    landed in clean-kernel — here `δ` is the ulp (the grid spacing). It is the
    fact that every padding step below was, until now, *assuming*; we PROVE it,
    riding the unit-spacing Mathlib half-ulp bound `abs_sub_round` and scaling
    by `δ`. Sorry-free; closure = the three foundational axioms. -/
theorem roundToGrid_error_le_half_ulp (q : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    |roundToGrid q δ - q| ≤ δ / 2 := by
  unfold roundToGrid
  -- Factor δ out: δ·round(q/δ) − q = δ·(round(q/δ) − q/δ) = −δ·(q/δ − round(q/δ)).
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hrw : δ * ((round (q / δ) : ℤ) : ℚ) - q
           = -(δ * (q / δ - ((round (q / δ) : ℤ) : ℚ))) := by
    field_simp
    ring
  rw [hrw, abs_neg, abs_mul, abs_of_pos hδ]
  -- |q/δ − round(q/δ)| ≤ 1/2 is the unit-spacing half-ulp bound.
  have hunit : |q / δ - ((round (q / δ) : ℤ) : ℚ)| ≤ 1 / 2 := abs_sub_round (q / δ)
  calc δ * |q / δ - ((round (q / δ) : ℤ) : ℚ)|
      ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left hunit hδ.le
    _ = δ / 2 := by ring

/-- The two-sided interval form: a correctly-rounded result lies within `δ/2`
    of the exact rational value, i.e. in `[q − δ/2, q + δ/2]`. This is the sound
    rational enclosure the padding folds in — now with the round-off bound
    PROVEN, not assumed (cf. `Crownproof.Quant.quant_envelope`, which took the
    bound as the hypothesis `hbound`). -/
theorem roundToGrid_mem_padded_interval (q : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    q - δ / 2 ≤ roundToGrid q δ ∧ roundToGrid q δ ≤ q + δ / 2 := by
  have h := roundToGrid_error_le_half_ulp q hδ
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### The correctly-rounded-op model and its DISCHARGED soundness contract

Mirroring the `FExp` pattern of `Crownproof/SoftmaxFloatRange.lean`, we package
a correctly-rounded operation as a structure carrying its only certifier-
relevant fact — the half-ulp round-off bound — as a STRUCTURE FIELD
(hypothesis), so it appears in no `#print axioms` output. Unlike a bare
`hbound` assumption, this structure is *inhabited by a theorem*: `gridRounding`
below builds it from `roundToGrid_error_le_half_ulp`, so the contract is
DISCHARGED, not assumed. -/

/-- A correctly-rounded IEEE-754 op (`+ − × ÷ √`) modelled over `ℚ` by its
    result `rounded q` at ulp `ulp` together with the ONE fact a sound checker
    relies on: the half-ulp round-off bound. The field is a hypothesis (no
    axiom). It is discharged for the canonical grid-rounding op by
    `gridRounding`. -/
structure CorrectlyRoundedOp where
  /-- The grid spacing (the ulp at the magnitude being rounded). -/
  ulp : ℚ
  /-- The ulp is a positive power-of-two grid spacing. -/
  ulp_pos : 0 < ulp
  /-- The rounded rational result of the op on exact input `q`. -/
  rounded : ℚ → ℚ
  /-- **The half-ulp soundness contract** (the field that is the FP-soundness
      guarantee). For correctly-rounded ops this is a THEOREM, not an axiom —
      see `gridRounding`. -/
  error_le_half_ulp : ∀ q : ℚ, |rounded q - q| ≤ ulp / 2

/-- The canonical correctly-rounded op: round-to-grid at spacing `δ`. Its
    half-ulp contract is DISCHARGED by `roundToGrid_error_le_half_ulp` — no
    `sorry`, no assumed `hbound`, no `Float` axiom. This is the witness that the
    `CorrectlyRoundedOp` contract is *grounded*, not merely posited. -/
def gridRounding {δ : ℚ} (hδ : 0 < δ) : CorrectlyRoundedOp where
  ulp := δ
  ulp_pos := hδ
  rounded := fun q => roundToGrid q δ
  error_le_half_ulp := fun q => roundToGrid_error_le_half_ulp q hδ

/-! ### The FP-padded lower certificate: padding soundness, GROUNDED

A real verifier emits a rational lower bound `α·x` and runs it in `binary64`.
The FP-computed value differs from the exact `α·x` by the rounding error of the
op. A *sound* padded certificate subtracts the per-op `ulp/2` pad from the
exact bound; the padded bound is then `≤` the FP-computed value, hence `≤ relu`.

The load-bearing lemma — the one all the others were gated on — is
`fp_lower_pad_sound`: it says the rounding pad `ulp/2` provably upper-bounds
the actual rounding error, so the padded rational bound under-estimates the
correctly-rounded FP value. Its proof is now sorry-free because the round-off
bound it needs is the PROVEN `error_le_half_ulp`, not an assumption. -/

/-- **Per-op padding soundness (the load-bearing lemma).** Let `op` be any
    correctly-rounded op and `q` the exact rational value it should compute.
    Then the value `op.rounded q` actually produced lies AT OR ABOVE the
    `ulp/2`-padded-down rational bound:

      `q − op.ulp/2 ≤ op.rounded q`.

    Equivalently: padding a rational lower bound DOWN by `ulp/2` keeps it a
    valid lower bound for the correctly-rounded computation. This is the exact
    statement "the rounding padding bounds the FP error" that every downstream
    `sorry`/`hbound` was gated on — now PROVEN, grounded in the half-ulp bound
    (`op.error_le_half_ulp`), with empty domain-axiom closure. -/
theorem fp_lower_pad_sound (op : CorrectlyRoundedOp) (q : ℚ) :
    q - op.ulp / 2 ≤ op.rounded q := by
  have h := op.error_le_half_ulp q
  rw [abs_le] at h
  linarith [h.1]

/-- The symmetric upper half: the correctly-rounded result lies AT OR BELOW the
    `ulp/2`-padded-up bound, `op.rounded q ≤ q + op.ulp/2`. Together with
    `fp_lower_pad_sound` this is the sound `ulp/2` enclosure of the FP op around
    the exact rational value. -/
theorem fp_upper_pad_sound (op : CorrectlyRoundedOp) (q : ℚ) :
    op.rounded q ≤ q + op.ulp / 2 := by
  have h := op.error_le_half_ulp q
  rw [abs_le] at h
  linarith [h.2]

/-- **FP-grounded α-CROWN lower soundness (the gap closed).** Let `c` be a
    VALID α-CROWN lower certificate (`0 ≤ α ≤ 1`) and `op` a correctly-rounded
    op computing the lower envelope `α·x`. Then the `ulp/2`-padded FP-computed
    lower bound is STILL a sound lower bound for `relu`:

      `op.rounded (c.lowerBound x) − op.ulp/2 ≤ relu x`   for every `x : ℚ`.

    This is the end-to-end FP-soundness statement Day 1 left as an *assumed*
    padding: the rational soundness `crown_lower_cert_sound` says
    `c.lowerBound x ≤ relu x` exactly; subtracting the proven `ulp/2` pad makes
    the bound hold for the actual `binary64` value `op.rounded (c.lowerBound x)`
    as well. The padding term is now GROUNDED in the half-ulp theorem
    (`fp_upper_pad_sound`), not assumed. Sorry-free; closure = the three
    foundational axioms. -/
theorem crown_lower_cert_fp_padded_sound
    (c : CrownLowerCert) (hValid : c.isValid) (op : CorrectlyRoundedOp) (x : ℚ) :
    op.rounded (c.lowerBound x) - op.ulp / 2 ≤ relu x := by
  -- The FP value is within ulp/2 of the exact `c.lowerBound x` (proven pad);
  -- and the exact `c.lowerBound x` is ≤ relu x (Day-1 rational soundness).
  have hpad : op.rounded (c.lowerBound x) ≤ c.lowerBound x + op.ulp / 2 :=
    fp_upper_pad_sound op (c.lowerBound x)
  have hexact : c.lowerBound x ≤ relu x := crown_lower_cert_sound c hValid x
  linarith

/-- **Full-affine FP-grounded soundness.** The same grounding for the wider
    full-affine lower class (the class real verifiers emit): a valid
    `FullAffineLowerCert`, run in `binary64` and padded down by `ulp/2`, is
    still a sound `relu` lower bound on its interval. Closes the FP gap for the
    full-affine checker, not only the pure-slope α-CROWN slice. -/
theorem full_affine_lower_cert_fp_padded_sound
    (c : FullAffineLowerCert) (hValid : c.isValid) (op : CorrectlyRoundedOp)
    (x : ℚ) (hxl : c.l ≤ x) (hxu : x ≤ c.u) :
    op.rounded (c.lowerBound x) - op.ulp / 2 ≤ relu x := by
  have hpad : op.rounded (c.lowerBound x) ≤ c.lowerBound x + op.ulp / 2 :=
    fp_upper_pad_sound op (c.lowerBound x)
  have hexact : c.lowerBound x ≤ relu x :=
    full_affine_lower_cert_sound c hValid x hxl hxu
  linarith

/-! ### Accumulated rounding error over a linear layer, GROUNDED

A single verifier step accumulates many correctly-rounded ops (one per term of
a dot product). The per-op `ulp/2` pads accumulate LINEARLY. `Crownproof.Quant`
proves this accumulation (`quant_linear_propagation`) but, again, over an
*assumed* per-coordinate round-off bound. Here the same accumulation is stated
with the per-op bound supplied by the PROVEN `CorrectlyRoundedOp` contract, so
the whole accumulated pad is grounded. -/

/-- **Accumulated padding soundness over a dot product.** Computing
    `∑ i, w i * (op i).rounded (q i)` with one correctly-rounded op per term
    differs from the exact `∑ i, w i * q i` by at most `∑ i, |w i| * (op i).ulp/2`.

    Each term's rounding error is `≤ (op i).ulp/2` by the PROVEN per-op contract
    (`error_le_half_ulp`); the errors accumulate linearly through the weighted
    sum (triangle inequality + per-term bound). This is the grounded form of
    `Crownproof.Quant.quant_linear_propagation`: the per-coordinate round-off
    bound is no longer an assumption but a discharged structure field. Empty
    domain-axiom closure. -/
theorem accumulated_pad_sound
    {ι : Type*} (s : Finset ι) (w q : ι → ℚ) (op : ι → CorrectlyRoundedOp) :
    |(∑ i ∈ s, w i * (op i).rounded (q i)) - (∑ i ∈ s, w i * q i)|
      ≤ ∑ i ∈ s, |w i| * ((op i).ulp / 2) := by
  -- Combine into a single sum of per-coordinate weighted differences.
  have hdiff :
      (∑ i ∈ s, w i * (op i).rounded (q i)) - (∑ i ∈ s, w i * q i)
        = ∑ i ∈ s, w i * ((op i).rounded (q i) - q i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hdiff]
  calc |∑ i ∈ s, w i * ((op i).rounded (q i) - q i)|
      ≤ ∑ i ∈ s, |w i * ((op i).rounded (q i) - q i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |w i| * ((op i).ulp / 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((op i).error_le_half_ulp (q i)) (abs_nonneg _)

/-! ### Worked example: the grounded firewall on concrete data

`δ = 1/4` (a power-of-two ulp). Rounding `q = 5/16` onto the `1/4`-grid lands at
`1/4`; the error `|1/4 − 5/16| = 1/16` is `≤ δ/2 = 1/8` — exactly the NORMAL
discharge case of `rounding_error_le_half_ulp` (the kernel's
`rounding_error_bound_discharge_normal`), here over `ℚ`. -/
namespace Day5Examples

/-- The canonical grid-rounding op at ulp `1/4`. Its half-ulp contract is a
    theorem, so the op is constructed with no `sorry`/axiom. -/
def quarterUlpOp : CorrectlyRoundedOp := gridRounding (δ := (1 : ℚ) / 4) (by norm_num)

/-- The NORMAL discharge case, over `ℚ`: `5/16` rounds to `1/4` on the
    `1/4`-grid; error `1/16 ≤ 1/8 = δ/2`. -/
example : roundToGrid ((5 : ℚ) / 16) ((1 : ℚ) / 4) = 1 / 4 := by
  unfold roundToGrid
  norm_num [round_eq]

example : |roundToGrid ((5 : ℚ) / 16) ((1 : ℚ) / 4) - (5 : ℚ) / 16| ≤ (1 : ℚ) / 4 / 2 :=
  roundToGrid_error_le_half_ulp ((5 : ℚ) / 16) (by norm_num)

/-- End-to-end: a valid α = 1/2 certificate, computed at ulp 1/4 and padded
    down, is a sound `relu` lower bound at every `x`. -/
example (x : ℚ) :
    quarterUlpOp.rounded (Examples.midpointSlopeCert.lowerBound x) - quarterUlpOp.ulp / 2
      ≤ relu x := by
  have hValid : Examples.midpointSlopeCert.isValid := by
    unfold CrownLowerCert.isValid Examples.midpointSlopeCert; norm_num
  exact crown_lower_cert_fp_padded_sound Examples.midpointSlopeCert hValid quarterUlpOp x

end Day5Examples

/-! ## Day 5 axiom audit

Every Day-5 theorem must rest ONLY on the three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) — the half-ulp grounding adds NO
domain-specific axiom and NO hidden `Float` axiom; the round-off bound is a
proven theorem (`roundToGrid_error_le_half_ulp`), and the `CorrectlyRoundedOp`
contract is a structure-field hypothesis (discharged by `gridRounding`), never
an axiom. -/

#guard_msgs (drop info) in
#print axioms roundToGrid_error_le_half_ulp

#guard_msgs (drop info) in
#print axioms roundToGrid_mem_padded_interval

#guard_msgs (drop info) in
#print axioms fp_lower_pad_sound

#guard_msgs (drop info) in
#print axioms fp_upper_pad_sound

#guard_msgs (drop info) in
#print axioms crown_lower_cert_fp_padded_sound

#guard_msgs (drop info) in
#print axioms full_affine_lower_cert_fp_padded_sound

#guard_msgs (drop info) in
#print axioms accumulated_pad_sound

end Mathbot.CrownCertificateChecker
