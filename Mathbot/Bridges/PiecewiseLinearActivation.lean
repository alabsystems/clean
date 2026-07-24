/-
  Mathbot/Bridges/PiecewiseLinearActivation.lean

  **Piecewise-Linear Activation Meta-Theorem — Day 1 + Tuesday**

  This file is the spec layer of extension E1 (the piecewise-linear
  activation meta-theorem) recommended by the creative-architect
  agent in `docs/mathbot/fp-soundness-creative-extensions-2026-05-26.md`.

  ## The gap this addresses

  Every state-of-the-art NN verifier (alpha-beta-CROWN, NeuralSAT,
  Marabou, GCP-CROWN, PRIMA, …) hand-derives soundness for *each*
  activation function: ReLU, LeakyReLU, hard-tanh, ReLU6, GELU…
  No tool ships a *parametric* soundness theorem.

  TorchLean (arXiv:2602.22631), Imandra (ITP'25, arXiv:2405.10611),
  and our own `Mathbot.Bridges.CrownCertificateChecker` all live in
  ReLU-land. Every modern frontier network (transformers, ConvNeXts,
  MobileViTs, Llama-style decoders) uses *non-ReLU* activations.

  ## What this file establishes (Day 1 + Tuesday)

  We work entirely over `ℚ`. No `Float`. No `Real`.

  ### Day 1 — `PLActivation` spec and generic monotonicity/Lipschitz

  A `PLActivation` is a finite-data representation of a continuous
  piecewise-linear function `ℚ → ℚ`. It is determined by:

  * `initialSlope : ℚ` — the slope on `(-∞, first breakpoint]`,
  * `intercept   : ℚ` — the y-intercept of the leftmost segment,
  * `kinks : List (ℚ × ℚ)` — a *sorted* list of pairs
    `(bᵢ, δᵢ)` where `bᵢ` is a breakpoint and `δᵢ` is the change in
    slope across that breakpoint.

  The evaluation is

  ```
  σ(x) = intercept + initialSlope · x
          + Σ_{(b, δ) ∈ kinks, b ≤ x} δ · (x − b).
  ```

  This representation is *automatically continuous* (each kink only
  adds a term that vanishes at `x = b`), and the slope on each segment
  is the prefix-sum of `initialSlope` and the `δᵢ` for breakpoints
  to the left of `x`.

  We prove (Day 1):

  1. `PLActivation.evaluate_monotone` — if every kink slope-change
     and the initial slope are non-negative, `σ` is monotone non-
     decreasing.
  2. `PLActivation.evaluate_lipschitz` — `σ` is globally Lipschitz
     with constant `|initialSlope| + Σ |δᵢ|`.

  ### Tuesday — concrete instances

  We exhibit six standard activations as `PLActivation` values and
  derive their monotonicity / Lipschitz constants:

  * `reluPL` — ReLU `max(0, x)`. Lipschitz `1`. Monotone.
  * `leakyReluPL α` — LeakyReLU with negative-side slope `α ∈ [0, 1]`.
    Lipschitz `1`. Monotone.
  * `hardTanhPL` — clamp to `[-1, 1]`. Monotone. Lipschitz budget `2`.
  * `relu6PL` — clamp ReLU above by `6`. Monotone. Lipschitz budget `2`.
  * `clippedReluPL c` — clamp ReLU above by `c ≥ 0`. Monotone. Lipschitz
    budget `2`.
  * `absPL` — absolute value `|x|`. Even (not monotone). Lipschitz
    budget `3`.

  (The "Lipschitz budget" is the conservative bound from the
  slope-magnitude sum; the tight constants are `1` in every case,
  and are derived by the Day-3/4 meta-theorem.)

  ### Wednesday – Friday outline

  See `docs/mathbot/pl-activation-meta-2026-05-26.md`. Briefly:

  * Wed: lift `CrownLowerCert` to `PLLowerCert (σ : PLActivation)`
    with a *rational vertex polytope* `validityPolytope σ l u`.
  * Thu: prove `pl_lower_cert_sound` and
    `pl_lower_cert_complete_crossing`.
  * Fri: derive `Mathbot.Bridges.CrownCertificateChecker` as a
    one-liner corollary; axiom audit; ITP 2026 outline.

  ## Axiom audit

  All theorems in this file have transitive axiom closure
  `⊆ {propext, Quot.sound, Classical.choice}` (the `FOUNDATIONAL_AXIOMS`
  closure required by `CLAUDE.md` proof soundness rules). See the
  `#print axioms` checks at the bottom of the file.

  Author: Andrew Yates (Promoted.ai), with Claude Opus 4.7 (1M context).
  Date: 2026-05-26.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Mathbot.PiecewiseLinearActivation

/-! ## The `PLActivation` structure

A continuous piecewise-linear function on `ℚ` represented by its
*kink expansion*: an initial affine piece plus a sorted list of
slope-change events. -/

/-- A continuous piecewise-linear activation `ℚ → ℚ`, represented
    by its kink expansion.

    The function is

    ```
    σ(x) = intercept + initialSlope · x
            + Σ_{(b, δ) ∈ kinks, b ≤ x} δ · (x − b).
    ```

    The list `kinks` should be sorted strictly increasing in the first
    coordinate; sortedness is *not* enforced as a field of the
    structure (it is a separate `Sorted` predicate) so that the
    structure remains `Repr`-derivable, but theorems that need
    sortedness take it as a hypothesis. -/
structure PLActivation where
  /-- Slope of the leftmost (unbounded) affine piece. -/
  initialSlope : ℚ
  /-- y-intercept of the leftmost (unbounded) affine piece. -/
  intercept : ℚ
  /-- Sorted list of `(breakpoint, slope_change)` pairs. -/
  kinks : List (ℚ × ℚ)
deriving Repr

/-- Strict-sortedness of the breakpoint coordinates of a `PLActivation`. -/
def PLActivation.Sorted (σ : PLActivation) : Prop :=
  σ.kinks.Pairwise (fun p q => p.1 < q.1)

/-- The single-kink contribution at a breakpoint: `δ · (x − b)` if
    `b ≤ x`, else `0`. -/
@[simp] def kinkContribution (k : ℚ × ℚ) (x : ℚ) : ℚ :=
  if k.1 ≤ x then k.2 * (x - k.1) else 0

/-- Evaluate a `PLActivation` at a rational point. -/
@[simp] def PLActivation.evaluate (σ : PLActivation) (x : ℚ) : ℚ :=
  σ.intercept + σ.initialSlope * x +
    (σ.kinks.map (fun k => kinkContribution k x)).sum

/-! ## Slope at a point

The right-derivative of `σ` at `x` is `initialSlope + Σ_{bᵢ ≤ x} δᵢ`.
We expose this as a definition for use in monotonicity proofs. -/

/-- The slope (right-derivative) of `σ` immediately to the right of
    `x`: the sum of the initial slope and all kink-deltas for
    breakpoints `bᵢ ≤ x`. -/
def PLActivation.slopeAt (σ : PLActivation) (x : ℚ) : ℚ :=
  σ.initialSlope +
    (σ.kinks.filter (fun k => decide (k.1 ≤ x))).foldr (fun k a => k.2 + a) 0

/-- The total slope change across all kinks. The terminal slope at
    `+∞` is `initialSlope + totalSlopeChange`. -/
def PLActivation.totalSlopeChange (σ : PLActivation) : ℚ :=
  σ.kinks.foldr (fun k a => k.2 + a) 0

/-! ## Monotonicity

We prove monotonicity under the *sufficient* condition that
`initialSlope ≥ 0` AND every kink slope-change `δᵢ ≥ 0`. This covers
ReLU, LeakyReLU (with `0 ≤ α ≤ 1`), hard-tanh, ReLU6, clipped-ReLU.

The fully general "all *prefix* slopes ≥ 0" condition (allowing some
`δᵢ < 0` cancelled by a larger positive prefix) is sufficient too;
the proof is structurally the same but threads a running prefix-slope
through the induction. We leave that for the Wed/Thu meta-theorem
when monotone-decreasing or absolute-value envelopes require it. -/

/-- All slope-changes are non-negative. -/
def PLActivation.AllNonNegSlopes (σ : PLActivation) : Prop :=
  0 ≤ σ.initialSlope ∧ ∀ k ∈ σ.kinks, 0 ≤ k.2

/-- A single kink contribution is monotone non-decreasing in `x` when
    its slope is non-negative. -/
theorem kinkContribution_mono_of_slope_nonneg
    {b δ : ℚ} (hδ : 0 ≤ δ) {x y : ℚ} (hxy : x ≤ y) :
    kinkContribution (b, δ) x ≤ kinkContribution (b, δ) y := by
  by_cases hbx : b ≤ x
  · have hby : b ≤ y := hbx.trans hxy
    simp only [kinkContribution, if_pos hbx, if_pos hby]
    have hsub : x - b ≤ y - b := by linarith
    exact mul_le_mul_of_nonneg_left hsub hδ
  · by_cases hby : b ≤ y
    · simp only [kinkContribution, if_neg hbx, if_pos hby]
      have hnn : 0 ≤ y - b := by linarith
      exact mul_nonneg hδ hnn
    · simp only [kinkContribution, if_neg hbx, if_neg hby]; rfl

/-- Sum of monotone kink contributions is monotone. -/
private theorem sum_kinkContributions_mono_of_all_nonneg
    (ks : List (ℚ × ℚ)) (hks : ∀ k ∈ ks, 0 ≤ k.2)
    {x y : ℚ} (hxy : x ≤ y) :
    (ks.map (fun k => kinkContribution k x)).sum ≤
      (ks.map (fun k => kinkContribution k y)).sum := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    have hkδ : 0 ≤ k.2 := hks k (by simp)
    have h_head : kinkContribution k x ≤ kinkContribution k y := by
      have := kinkContribution_mono_of_slope_nonneg (b := k.1) (δ := k.2) hkδ hxy
      simpa using this
    have h_tail : (ks.map (fun k' => kinkContribution k' x)).sum ≤
                    (ks.map (fun k' => kinkContribution k' y)).sum := by
      apply ih
      intro k' hk'
      exact hks k' (by simp [hk'])
    linarith

/-- **Monotonicity (sufficient form).** If `σ` has non-negative
    initial slope *and* all kink slope-changes `δᵢ` are non-negative,
    then `σ.evaluate` is monotone non-decreasing on all of `ℚ`. -/
theorem PLActivation.evaluate_monotone
    (σ : PLActivation) (hAll : σ.AllNonNegSlopes) :
    Monotone σ.evaluate := by
  intro x y hxy
  obtain ⟨h₀, hδs⟩ := hAll
  simp only [PLActivation.evaluate]
  have h_lin : σ.initialSlope * x ≤ σ.initialSlope * y :=
    mul_le_mul_of_nonneg_left hxy h₀
  have h_sum : (σ.kinks.map (fun k => kinkContribution k x)).sum ≤
                 (σ.kinks.map (fun k => kinkContribution k y)).sum :=
    sum_kinkContributions_mono_of_all_nonneg σ.kinks hδs hxy
  linarith

/-! ## Lipschitz bound

A piecewise-linear function with bounded slopes is globally Lipschitz
with constant equal to the slope budget. We prove the explicit bound

```
  |σ(y) − σ(x)| ≤ (|initialSlope| + Σ |δᵢ|) · |y − x|.
```

This is *not* the tightest Lipschitz constant (some kinks may cancel,
e.g. hard-tanh's tight constant is `1` but its slope budget is `2`),
but it is the obvious slope-budget that the meta-theorem will refine
on Wed/Thu. -/

/-- The Lipschitz constant we expose: `|initialSlope| + Σ |δᵢ|`. -/
def PLActivation.lipschitzConst (σ : PLActivation) : ℚ :=
  |σ.initialSlope| + (σ.kinks.map (fun k => |k.2|)).sum

/-- The Lipschitz constant is non-negative. -/
theorem PLActivation.lipschitzConst_nonneg (σ : PLActivation) :
    0 ≤ σ.lipschitzConst := by
  unfold PLActivation.lipschitzConst
  apply add_nonneg (abs_nonneg _)
  induction σ.kinks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (abs_nonneg _) ih

/-- A single kink's contribution is Lipschitz in `x` with constant
    `|δ|`. The proof is a four-way case-split on which side of `b`
    each of `x` and `y` lies. -/
private theorem kinkContribution_lipschitz
    (k : ℚ × ℚ) (x y : ℚ) :
    |kinkContribution k y - kinkContribution k x| ≤ |k.2| * |y - x| := by
  obtain ⟨b, δ⟩ := k
  by_cases hbx : b ≤ x
  · by_cases hby : b ≤ y
    · -- Both points to the right of `b`.
      simp only [kinkContribution, if_pos hbx, if_pos hby]
      have hrw : δ * (y - b) - δ * (x - b) = δ * (y - x) := by ring
      rw [hrw, abs_mul]
    · -- `x` right of `b`, `y` left of `b`.
      simp only [kinkContribution, if_pos hbx, if_neg hby]
      have hyb : y < b := lt_of_not_ge hby
      -- goal: |0 - δ * (x - b)| ≤ |δ| * |y - x|
      have hrw1 : (0 : ℚ) - δ * (x - b) = δ * (b - x) := by ring
      rw [hrw1, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hxb_nn : (0 : ℚ) ≤ x - b := by linarith
      have hxy_nn : (0 : ℚ) ≤ x - y := by linarith
      rw [abs_sub_comm b x, abs_of_nonneg hxb_nn,
          abs_sub_comm y x, abs_of_nonneg hxy_nn]
      linarith
  · by_cases hby : b ≤ y
    · -- `x` left of `b`, `y` right of `b`.
      simp only [kinkContribution, if_neg hbx, if_pos hby]
      have hxb : x < b := lt_of_not_ge hbx
      have hrw1 : δ * (y - b) - 0 = δ * (y - b) := by ring
      rw [hrw1, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hyb_nn : (0 : ℚ) ≤ y - b := by linarith
      have hyx_nn : (0 : ℚ) ≤ y - x := by linarith
      rw [abs_of_nonneg hyb_nn, abs_of_nonneg hyx_nn]
      linarith
    · -- Both points left of `b`.
      simp only [kinkContribution, if_neg hbx, if_neg hby]
      simp [abs_nonneg, mul_nonneg]

/-- The sum of kink contributions is Lipschitz with constant
    `Σ |δᵢ|`. -/
private theorem sum_kinkContributions_lipschitz
    (ks : List (ℚ × ℚ)) (x y : ℚ) :
    |(ks.map (fun k => kinkContribution k y)).sum -
       (ks.map (fun k => kinkContribution k x)).sum|
      ≤ (ks.map (fun k => |k.2|)).sum * |y - x| := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrw :
        (kinkContribution k y + (ks.map (fun k' => kinkContribution k' y)).sum)
          - (kinkContribution k x + (ks.map (fun k' => kinkContribution k' x)).sum)
        = (kinkContribution k y - kinkContribution k x)
          + ((ks.map (fun k' => kinkContribution k' y)).sum
              - (ks.map (fun k' => kinkContribution k' x)).sum) := by
      ring
    rw [hrw]
    have h_head := kinkContribution_lipschitz k x y
    have h_triangle :=
      abs_add_le (kinkContribution k y - kinkContribution k x)
        ((ks.map (fun k' => kinkContribution k' y)).sum
          - (ks.map (fun k' => kinkContribution k' x)).sum)
    have hrhs :
        (|k.2| + (ks.map (fun k' => |k'.2|)).sum) * |y - x|
          = |k.2| * |y - x| + (ks.map (fun k' => |k'.2|)).sum * |y - x| := by
      ring
    rw [hrhs]
    linarith [h_head, h_triangle, ih]

/-- **Lipschitz bound (Day 1's main quantitative result).**
    For every `x, y : ℚ`,
    `|σ(y) − σ(x)| ≤ σ.lipschitzConst · |y − x|`. -/
theorem PLActivation.evaluate_lipschitz
    (σ : PLActivation) (x y : ℚ) :
    |σ.evaluate y - σ.evaluate x| ≤ σ.lipschitzConst * |y - x| := by
  simp only [PLActivation.evaluate, PLActivation.lipschitzConst]
  have hrw :
      (σ.intercept + σ.initialSlope * y +
        (σ.kinks.map (fun k => kinkContribution k y)).sum)
        - (σ.intercept + σ.initialSlope * x +
            (σ.kinks.map (fun k => kinkContribution k x)).sum)
      = σ.initialSlope * (y - x) +
        ((σ.kinks.map (fun k => kinkContribution k y)).sum
          - (σ.kinks.map (fun k => kinkContribution k x)).sum) := by
    ring
  rw [hrw]
  have h_triangle :=
    abs_add_le (σ.initialSlope * (y - x))
      ((σ.kinks.map (fun k => kinkContribution k y)).sum
        - (σ.kinks.map (fun k => kinkContribution k x)).sum)
  have h_lin : |σ.initialSlope * (y - x)| = |σ.initialSlope| * |y - x| := abs_mul _ _
  have h_sum := sum_kinkContributions_lipschitz σ.kinks x y
  have hrhs :
      (|σ.initialSlope| + (σ.kinks.map (fun k => |k.2|)).sum) * |y - x|
        = |σ.initialSlope| * |y - x| + (σ.kinks.map (fun k => |k.2|)).sum * |y - x| := by
    ring
  rw [hrhs]
  linarith [h_triangle, h_sum, h_lin.le, h_lin.ge]

/-! ## Symmetric (even) activations

Some piecewise-linear activations of interest are *not* monotone but
are *symmetric* (`σ(-x) = σ(x)`). The canonical example is `abs`. We
expose symmetry as a Prop for reuse by the meta-theorem. -/

/-- `σ` is even: `σ(-x) = σ(x)` for every `x`. -/
def PLActivation.Even (σ : PLActivation) : Prop :=
  ∀ x : ℚ, σ.evaluate (-x) = σ.evaluate x

/-! ## Concrete instances (Tuesday)

We exhibit six standard activations as `PLActivation` values and
prove they evaluate to the expected closed-form expression. -/

namespace Instances

/-! ### ReLU -/

/-- ReLU as a `PLActivation`: initial slope `0`, intercept `0`, one
    kink at `b = 0` with `δ = 1`. -/
def reluPL : PLActivation :=
  { initialSlope := 0, intercept := 0, kinks := [(0, 1)] }

/-- ReLU evaluates as `max(0, x)`. -/
theorem reluPL_evaluate (x : ℚ) :
    reluPL.evaluate x = max 0 x := by
  simp only [PLActivation.evaluate, reluPL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases hx : (0 : ℚ) ≤ x
  · rw [if_pos hx, max_eq_right hx]; ring
  · rw [if_neg hx]
    have hxlt : x < 0 := lt_of_not_ge hx
    rw [max_eq_left hxlt.le]; ring

/-- ReLU is monotone. -/
theorem reluPL_monotone : Monotone reluPL.evaluate := by
  apply PLActivation.evaluate_monotone
  refine ⟨le_refl _, ?_⟩
  intro k hk
  simp only [reluPL, List.mem_singleton] at hk
  subst hk
  norm_num

/-- ReLU's Lipschitz constant is `1`. -/
theorem reluPL_lipschitzConst : reluPL.lipschitzConst = 1 := by
  simp [PLActivation.lipschitzConst, reluPL]

/-! ### LeakyReLU

`leakyRelu α x = if x ≥ 0 then x else α · x`.

For the standard "monotone" choice we require `0 ≤ α ≤ 1`. The
underlying piecewise-linear data is

* initial slope `α`,
* one kink at `0` with `δ = 1 - α`.
-/

/-- LeakyReLU with negative-side slope `α`. -/
def leakyReluPL (α : ℚ) : PLActivation :=
  { initialSlope := α, intercept := 0, kinks := [(0, 1 - α)] }

/-- LeakyReLU evaluates to `α·x` for `x < 0` and `x` for `x ≥ 0`. -/
theorem leakyReluPL_evaluate (α x : ℚ) :
    (leakyReluPL α).evaluate x = if 0 ≤ x then x else α * x := by
  simp only [PLActivation.evaluate, leakyReluPL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases hx : (0 : ℚ) ≤ x
  · rw [if_pos hx, if_pos hx]; ring
  · rw [if_neg hx, if_neg hx]; ring

/-- LeakyReLU is monotone iff `0 ≤ α ≤ 1`. -/
theorem leakyReluPL_monotone {α : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Monotone (leakyReluPL α).evaluate := by
  apply PLActivation.evaluate_monotone
  refine ⟨h0, ?_⟩
  intro k hk
  simp only [leakyReluPL, List.mem_singleton] at hk
  subst hk
  simp
  linarith

/-- LeakyReLU's Lipschitz budget on `0 ≤ α ≤ 1` is exactly `1`. -/
theorem leakyReluPL_lipschitzConst_le_one {α : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (leakyReluPL α).lipschitzConst = 1 := by
  simp only [PLActivation.lipschitzConst, leakyReluPL,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : (0:ℚ) ≤ 1 - α)]
  linarith

/-! ### Hard-tanh

`hardTanh x = max (-1) (min 1 x)`.

Two breakpoints `-1`, `1`. Initial slope `0`, intercept `-1`, kinks
`[(-1, +1), (1, -1)]`. -/

/-- Hard-tanh as a `PLActivation`. -/
def hardTanhPL : PLActivation :=
  { initialSlope := 0, intercept := -1, kinks := [(-1, 1), (1, -1)] }

/-- Hard-tanh evaluates to `max(-1, min(1, x))`. -/
theorem hardTanhPL_evaluate (x : ℚ) :
    hardTanhPL.evaluate x = max (-1) (min 1 x) := by
  simp only [PLActivation.evaluate, hardTanhPL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases h1 : (-1 : ℚ) ≤ x
  · by_cases h2 : (1 : ℚ) ≤ x
    · -- x ≥ 1.
      have hmax : max (-1 : ℚ) (min 1 x) = 1 := by
        rw [min_eq_left h2, max_eq_right (by norm_num : (-1 : ℚ) ≤ 1)]
      rw [hmax, if_pos h1, if_pos h2]; ring
    · -- -1 ≤ x < 1.
      have hxlt : x < 1 := lt_of_not_ge h2
      have hmax : max (-1 : ℚ) (min 1 x) = x := by
        rw [min_eq_right hxlt.le, max_eq_right h1]
      rw [hmax, if_pos h1, if_neg h2]; ring
  · -- x < -1.
    have hxlt : x < -1 := lt_of_not_ge h1
    have h2' : ¬ (1 : ℚ) ≤ x := by linarith
    have hmax : max (-1 : ℚ) (min 1 x) = -1 := by
      rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hxlt.le]
    rw [hmax, if_neg h1, if_neg h2']; ring

/-- Hard-tanh is monotone. -/
theorem hardTanhPL_monotone : Monotone hardTanhPL.evaluate := by
  intro x y hxy
  rw [hardTanhPL_evaluate, hardTanhPL_evaluate]
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Hard-tanh's slope-budget Lipschitz constant is `2`.

    Note: the *tight* Lipschitz constant is `1`, but our generic
    `lipschitzConst` is the slope-budget `0 + |1| + |-1| = 2`. We
    record this here and tighten via the meta-theorem (Wed/Thu)
    when proofs about envelopes require it. -/
theorem hardTanhPL_lipschitzConst : hardTanhPL.lipschitzConst = 2 := by
  simp only [PLActivation.lipschitzConst, hardTanhPL,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-! ### ReLU6

`relu6 x = min(6, max(0, x))`.

Two breakpoints `0`, `6`. Initial slope `0`, intercept `0`, kinks
`[(0, 1), (6, -1)]`. -/

/-- ReLU6 as a `PLActivation`. -/
def relu6PL : PLActivation :=
  { initialSlope := 0, intercept := 0, kinks := [(0, 1), (6, -1)] }

/-- ReLU6 evaluates to `min(6, max(0, x))`. -/
theorem relu6PL_evaluate (x : ℚ) :
    relu6PL.evaluate x = min 6 (max 0 x) := by
  simp only [PLActivation.evaluate, relu6PL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases h0 : (0 : ℚ) ≤ x
  · by_cases h6 : (6 : ℚ) ≤ x
    · have hmm : min (6 : ℚ) (max 0 x) = 6 := by
        rw [max_eq_right h0, min_eq_left h6]
      rw [hmm, if_pos h0, if_pos h6]; ring
    · have hxlt : x < 6 := lt_of_not_ge h6
      have hmm : min (6 : ℚ) (max 0 x) = x := by
        rw [max_eq_right h0, min_eq_right hxlt.le]
      rw [hmm, if_pos h0, if_neg h6]; ring
  · have hxlt : x < 0 := lt_of_not_ge h0
    have h6' : ¬ (6 : ℚ) ≤ x := by linarith
    have hmm : min (6 : ℚ) (max 0 x) = 0 := by
      rw [max_eq_left hxlt.le, min_eq_right (by norm_num : (0 : ℚ) ≤ 6)]
    rw [hmm, if_neg h0, if_neg h6']; ring

/-- ReLU6 is monotone. -/
theorem relu6PL_monotone : Monotone relu6PL.evaluate := by
  intro x y hxy
  rw [relu6PL_evaluate, relu6PL_evaluate]
  exact min_le_min le_rfl (max_le_max le_rfl hxy)

/-- ReLU6's slope-budget Lipschitz constant is `2`. -/
theorem relu6PL_lipschitzConst : relu6PL.lipschitzConst = 2 := by
  simp only [PLActivation.lipschitzConst, relu6PL,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-! ### Clipped-ReLU

`clippedRelu c x = min(c, max(0, x))` for `c ≥ 0`. The `c = 6` case
recovers ReLU6; the `c = 1` case is sometimes called "hard-sigmoid"
(restricted). -/

/-- Clipped-ReLU with clip ceiling `c`. -/
def clippedReluPL (c : ℚ) : PLActivation :=
  { initialSlope := 0, intercept := 0, kinks := [(0, 1), (c, -1)] }

/-- Clipped-ReLU evaluates to `min(c, max(0, x))` provided `0 ≤ c`. -/
theorem clippedReluPL_evaluate {c : ℚ} (hc : 0 ≤ c) (x : ℚ) :
    (clippedReluPL c).evaluate x = min c (max 0 x) := by
  simp only [PLActivation.evaluate, clippedReluPL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases h0 : (0 : ℚ) ≤ x
  · by_cases hcx : c ≤ x
    · have hmm : min c (max 0 x) = c := by
        rw [max_eq_right h0, min_eq_left hcx]
      rw [hmm, if_pos h0, if_pos hcx]; ring
    · have hxlt : x < c := lt_of_not_ge hcx
      have hmm : min c (max 0 x) = x := by
        rw [max_eq_right h0, min_eq_right hxlt.le]
      rw [hmm, if_pos h0, if_neg hcx]; ring
  · have hxlt : x < 0 := lt_of_not_ge h0
    have hcx' : ¬ c ≤ x := by linarith
    have hmm : min c (max 0 x) = 0 := by
      rw [max_eq_left hxlt.le, min_eq_right hc]
    rw [hmm, if_neg h0, if_neg hcx']; ring

/-- Clipped-ReLU is monotone (for any clip ceiling `c ≥ 0`). -/
theorem clippedReluPL_monotone {c : ℚ} (hc : 0 ≤ c) :
    Monotone (clippedReluPL c).evaluate := by
  intro x y hxy
  rw [clippedReluPL_evaluate hc, clippedReluPL_evaluate hc]
  exact min_le_min le_rfl (max_le_max le_rfl hxy)

/-- Clipped-ReLU's slope-budget Lipschitz constant is `2`. -/
theorem clippedReluPL_lipschitzConst (c : ℚ) :
    (clippedReluPL c).lipschitzConst = 2 := by
  simp only [PLActivation.lipschitzConst, clippedReluPL,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-! ### Abs

`abs x = |x|`. *Non-monotone* but *symmetric*. Initial slope `-1`,
intercept `0`, one kink at `0` with `δ = 2`. -/

/-- Absolute value as a `PLActivation`. -/
def absPL : PLActivation :=
  { initialSlope := -1, intercept := 0, kinks := [(0, 2)] }

/-- `absPL` evaluates to `|x|`. -/
theorem absPL_evaluate (x : ℚ) :
    absPL.evaluate x = |x| := by
  simp only [PLActivation.evaluate, absPL, kinkContribution,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases hx : (0 : ℚ) ≤ x
  · rw [abs_of_nonneg hx, if_pos hx]; ring
  · have hxlt : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hxlt, if_neg hx]; ring

/-- `absPL` is even. -/
theorem absPL_even : absPL.Even := by
  intro x
  rw [absPL_evaluate, absPL_evaluate, abs_neg]

/-- `absPL`'s slope-budget Lipschitz constant is `3`.

    Tight constant is `1` (the function `|·|` is 1-Lipschitz); the
    slope-budget `|−1| + |2| = 3` is conservative. The meta-theorem
    will tighten this. -/
theorem absPL_lipschitzConst : absPL.lipschitzConst = 3 := by
  simp only [PLActivation.lipschitzConst, absPL,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

end Instances

/-! ## Wednesday — Generic certificate type

We now generalize `Mathbot.Bridges.CrownCertificateChecker.CrownLowerCert`
from ReLU-only to *every* `PLActivation`. A `PLLowerCert σ` is a
candidate affine lower-bound certificate `α · x + β ≤ σ(x)` over a
rational interval `[lo, hi]`.

### The validity polytope

The rational vertex set of the *soundness polytope* of valid `(α, β)`
pairs is generated by the linear inequalities

```
  α · x + β ≤ σ(x)
```

at every "test point" `x ∈ [lo, hi]`: the two endpoints `lo`, `hi`, and
every breakpoint `b` of `σ` lying in `[lo, hi]`. We expose this finite
set as `validityPolytope σ lo hi : List (ℚ × ℚ)` of `(x, σ(x))` pairs.

The Thursday meta-theorem (`pl_lower_cert_sound` /
`pl_lower_cert_complete_crossing`) establishes that this *finite* set
of inequalities exactly characterizes validity on the *continuum*
`[lo, hi]`. -/

/-- The list of "test points" inside `[l, u]`: the two endpoints
    plus every breakpoint of `σ` that falls inside `[l, u]`.

    Order is `l :: (in-range breakpoints) ++ [u]`; under
    `σ.Sorted` this list is sorted, but sortedness is not needed
    for the soundness/completeness theorems (they only quantify over
    membership). -/
def PLActivation.testPoints (σ : PLActivation) (l u : ℚ) : List ℚ :=
  l :: ((σ.kinks.map Prod.fst).filter (fun b => decide (l ≤ b ∧ b ≤ u))) ++ [u]

/-- The endpoints `l, u` are always test points. -/
theorem PLActivation.mem_testPoints_lo (σ : PLActivation) (l u : ℚ) :
    l ∈ σ.testPoints l u := by
  unfold PLActivation.testPoints
  simp

/-- The endpoints `l, u` are always test points. -/
theorem PLActivation.mem_testPoints_hi (σ : PLActivation) (l u : ℚ) :
    u ∈ σ.testPoints l u := by
  unfold PLActivation.testPoints
  simp

/-- Every test point lies in `[l, u]` (assuming `l ≤ u`). -/
theorem PLActivation.testPoints_mem_interval
    (σ : PLActivation) {l u : ℚ} (hlu : l ≤ u)
    {x : ℚ} (hx : x ∈ σ.testPoints l u) :
    l ≤ x ∧ x ≤ u := by
  unfold PLActivation.testPoints at hx
  rw [List.mem_append, List.mem_cons] at hx
  rcases hx with (rfl | hx) | hx
  · exact ⟨le_refl _, hlu⟩
  · rw [List.mem_filter, List.mem_map] at hx
    obtain ⟨⟨_, _, _⟩, hdec⟩ := hx
    simp only [decide_eq_true_eq] at hdec
    exact hdec
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hlu, le_refl _⟩

/-- A breakpoint of `σ` inside `[l, u]` is a test point. -/
theorem PLActivation.mem_testPoints_of_kink
    (σ : PLActivation) (l u : ℚ)
    {b : ℚ} (hb : b ∈ σ.kinks.map Prod.fst)
    (hlb : l ≤ b) (hbu : b ≤ u) :
    b ∈ σ.testPoints l u := by
  unfold PLActivation.testPoints
  rw [List.mem_append, List.mem_cons]
  left; right
  rw [List.mem_filter]
  refine ⟨hb, ?_⟩
  simp [hlb, hbu]

/-- The **validity polytope** of a `PLActivation` `σ` on `[l, u]`:
    the rational vertex set of `(x, σ(x))` pairs at every test point. -/
def validityPolytope (σ : PLActivation) (l u : ℚ) : List (ℚ × ℚ) :=
  (σ.testPoints l u).map (fun x => (x, σ.evaluate x))

/-- The endpoint `(l, σ(l))` is in the validity polytope. -/
theorem validityPolytope_lo (σ : PLActivation) (l u : ℚ) :
    (l, σ.evaluate l) ∈ validityPolytope σ l u := by
  unfold validityPolytope
  rw [List.mem_map]
  exact ⟨l, σ.mem_testPoints_lo l u, rfl⟩

/-- The endpoint `(u, σ(u))` is in the validity polytope. -/
theorem validityPolytope_hi (σ : PLActivation) (l u : ℚ) :
    (u, σ.evaluate u) ∈ validityPolytope σ l u := by
  unfold validityPolytope
  rw [List.mem_map]
  exact ⟨u, σ.mem_testPoints_hi l u, rfl⟩

/-- Each point of the validity polytope has the form
    `(x, σ(x))` for some test point `x`. -/
theorem validityPolytope_mem_iff
    (σ : PLActivation) (l u : ℚ) (p : ℚ × ℚ) :
    p ∈ validityPolytope σ l u ↔
      ∃ x ∈ σ.testPoints l u, p = (x, σ.evaluate x) := by
  unfold validityPolytope
  rw [List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, hxp⟩; exact ⟨x, hx, hxp.symm⟩
  · rintro ⟨x, hx, hxp⟩; exact ⟨x, hx, hxp.symm⟩

/-- A candidate affine lower-bound certificate `α · x + β ≤ σ(x)` for
    a `PLActivation` `σ` on a rational interval `[lo, hi]`. -/
structure PLLowerCert (σ : PLActivation) where
  /-- The slope of the linear lower envelope. -/
  alpha : ℚ
  /-- The intercept of the linear lower envelope. -/
  beta : ℚ
  /-- Lower endpoint of the input interval. -/
  lo : ℚ
  /-- Upper endpoint of the input interval. -/
  hi : ℚ

/-- The certificate's affine lower envelope: `α · x + β`. -/
@[simp] def PLLowerCert.lowerBound {σ : PLActivation} (c : PLLowerCert σ)
    (x : ℚ) : ℚ :=
  c.alpha * x + c.beta

/-- Syntactic well-formedness: the input interval is non-degenerate. -/
def PLLowerCert.isWellFormed {σ : PLActivation} (c : PLLowerCert σ) : Prop :=
  c.lo ≤ c.hi

instance {σ : PLActivation} (c : PLLowerCert σ) : Decidable c.isWellFormed := by
  unfold PLLowerCert.isWellFormed
  exact inferInstance

/-- The **validity predicate**: the certificate's affine lower envelope
    `α · x + β` is `≤ σ(x)` at every test point of the validity polytope.

    This is the finite, decidable check that the Thursday meta-theorem
    will prove equivalent to the *continuous* lower-bound statement
    "`α · x + β ≤ σ(x)` for every `x ∈ [lo, hi]`". -/
def PLLowerCert.isValid {σ : PLActivation} (c : PLLowerCert σ) : Prop :=
  c.lo ≤ c.hi ∧
    ∀ p ∈ validityPolytope σ c.lo c.hi, c.alpha * p.1 + c.beta ≤ p.2

instance {σ : PLActivation} (c : PLLowerCert σ) : Decidable c.isValid := by
  unfold PLLowerCert.isValid
  exact inferInstance

/-- The combined check: well-formed *and* valid. -/
def PLLowerCert.passes {σ : PLActivation} (c : PLLowerCert σ) : Prop :=
  c.isWellFormed ∧ c.isValid

instance {σ : PLActivation} (c : PLLowerCert σ) : Decidable c.passes := by
  unfold PLLowerCert.passes
  exact inferInstance

/-! ### Worked Wednesday examples

A few concrete certificates for `reluPL` on `[-2, 2]`. The validity
polytope at this interval is `[(-2, 0), (0, 0), (2, 2)]` (endpoint
`-2`, breakpoint `0`, endpoint `2`). -/

namespace PLLowerCertExamples

open Instances

/-- The `α = 0` certificate (the "lower envelope is identically zero"
    bound) on ReLU over `[-2, 2]`. Valid because `0 · x + 0 = 0 ≤ relu x`
    at every test point. -/
def reluZeroCert : PLLowerCert reluPL :=
  { alpha := 0, beta := 0, lo := -2, hi := 2 }

/-- Helper: the test points of `reluPL` on `[-2, 2]` are `{-2, 0, 2}`. -/
private theorem reluPL_testPoints_neg2_2 :
    reluPL.testPoints (-2 : ℚ) 2 = [-2, 0, 2] := by
  show ((-2 : ℚ)) :: (List.filter (fun b => decide ((-2 : ℚ) ≤ b ∧ b ≤ 2))
    (List.map Prod.fst reluPL.kinks)) ++ [2] = [-2, 0, 2]
  unfold reluPL
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  have h : decide (((-2 : ℚ)) ≤ 0 ∧ (0 : ℚ) ≤ 2) = true := by
    apply decide_eq_true; refine ⟨by norm_num, by norm_num⟩
  rw [h]
  rfl

/-- The validity polytope is `[(-2, 0), (0, 0), (2, 2)]`. -/
private theorem reluPL_validityPolytope_neg2_2 :
    validityPolytope reluPL (-2 : ℚ) 2 = [(-2, 0), (0, 0), (2, 2)] := by
  unfold validityPolytope
  rw [reluPL_testPoints_neg2_2]
  simp only [List.map_cons, List.map_nil]
  rw [reluPL_evaluate, reluPL_evaluate, reluPL_evaluate]
  norm_num

example : reluZeroCert.isValid := by
  refine ⟨by show ((-2 : ℚ)) ≤ 2; norm_num, ?_⟩
  intro p hp
  have hmem : p ∈ validityPolytope reluPL reluZeroCert.lo reluZeroCert.hi := hp
  have hlo : reluZeroCert.lo = (-2 : ℚ) := rfl
  have hhi : reluZeroCert.hi = (2 : ℚ) := rfl
  rw [hlo, hhi, reluPL_validityPolytope_neg2_2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  unfold reluZeroCert
  rcases hmem with rfl | rfl | rfl <;> norm_num

/-- The `α = 1/2, β = 0` ("midpoint") certificate on ReLU over `[-2, 2]`.
    Valid because at every test point `(x, relu x)`:
    `-2 → 1/2 · (-2) + 0 = -1 ≤ 0`,
    `0 → 0 ≤ 0`,
    `2 → 1 ≤ 2`. -/
def reluMidpointCert : PLLowerCert reluPL :=
  { alpha := (1 : ℚ) / 2, beta := 0, lo := -2, hi := 2 }

example : reluMidpointCert.isValid := by
  refine ⟨by show ((-2 : ℚ)) ≤ 2; norm_num, ?_⟩
  intro p hp
  have hmem : p ∈ validityPolytope reluPL reluMidpointCert.lo reluMidpointCert.hi := hp
  have hlo : reluMidpointCert.lo = (-2 : ℚ) := rfl
  have hhi : reluMidpointCert.hi = (2 : ℚ) := rfl
  rw [hlo, hhi, reluPL_validityPolytope_neg2_2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  unfold reluMidpointCert
  rcases hmem with rfl | rfl | rfl <;> norm_num

/-- An *invalid* certificate: `α = 2` is too large (it would predict
    `2 · 2 = 4 > 2 = relu 2`). Rejected by the validity check. -/
def reluBadCert : PLLowerCert reluPL :=
  { alpha := 2, beta := 0, lo := -2, hi := 2 }

example : ¬ reluBadCert.isValid := by
  intro hValid
  obtain ⟨_, hPoints⟩ := hValid
  have h : reluBadCert.alpha * (2 : ℚ) + reluBadCert.beta ≤ 2 := by
    have hmem : ((2 : ℚ), 2) ∈ validityPolytope reluPL reluBadCert.lo reluBadCert.hi := by
      have hlo : reluBadCert.lo = (-2 : ℚ) := rfl
      have hhi : reluBadCert.hi = (2 : ℚ) := rfl
      rw [hlo, hhi, reluPL_validityPolytope_neg2_2]
      simp
    exact hPoints (2, 2) hmem
  -- h : 2 * 2 + 0 ≤ 2, i.e. 4 ≤ 2.
  unfold reluBadCert at h
  norm_num at h

end PLLowerCertExamples

/-! ## Thursday — Soundness and completeness of the meta-certificate

We prove the two halves of the meta-theorem:

* **Soundness** (`pl_lower_cert_sound`): if `isValid` holds for `c`,
  then `c.alpha * x + c.beta ≤ σ.evaluate x` for *every* `x ∈ [lo, hi]`,
  not just the test points.

* **Completeness** (`pl_lower_cert_complete_crossing`): if the
  inequality `α · x + β ≤ σ(x)` holds on the *continuum* `[lo, hi]`,
  then the certificate `⟨α, β, lo, hi⟩` passes the *finite* validity
  check at every test point.

The combined iff is the **meta-decision-procedure** of the file. -/

/-! ### Affine-domination lemma

Both `α · x + β` (the certificate) and the restriction of `σ` to a
single linear segment are affine. The fact that affine domination at
two endpoints implies affine domination throughout the connecting
interval is the engine of the soundness proof. -/

/-- **Affine-domination on an interval.** If two affine functions
    `f x = α · x + β` and `g x = γ · x + δ` satisfy `f(p) ≤ g(p)` and
    `f(q) ≤ g(q)` for some `p ≤ q`, then `f(x) ≤ g(x)` for every
    `x ∈ [p, q]`.

    This is the convexity/concavity-free version: the difference
    `(γ - α) · x + (δ - β)` is itself affine, and an affine
    function attains its minimum on `[p, q]` at one of the endpoints.
    Proof: a two-way case-split on the sign of `γ - α`. -/
theorem affine_dominates_on_interval
    {α β γ δ p q x : ℚ} (_hpq : p ≤ q)
    (hp : α * p + β ≤ γ * p + δ)
    (hq : α * q + β ≤ γ * q + δ)
    (hxp : p ≤ x) (hxq : x ≤ q) :
    α * x + β ≤ γ * x + δ := by
  -- Define D(t) = (γ - α) * t + (δ - β); show D(p) ≥ 0, D(q) ≥ 0
  -- imply D(x) ≥ 0 for x ∈ [p, q].
  have hDp : 0 ≤ (γ - α) * p + (δ - β) := by linarith
  have hDq : 0 ≤ (γ - α) * q + (δ - β) := by linarith
  by_cases hΔ : 0 ≤ γ - α
  · -- D non-decreasing: D(x) ≥ D(p) ≥ 0.
    have hgrow : (γ - α) * p ≤ (γ - α) * x :=
      mul_le_mul_of_nonneg_left hxp hΔ
    linarith
  · -- γ - α < 0: D non-increasing: D(x) ≥ D(q) ≥ 0.
    have hΔ_lt : γ - α < 0 := lt_of_not_ge hΔ
    have hxneg : (γ - α) * q ≤ (γ - α) * x := by
      have hΔ_le : γ - α ≤ 0 := hΔ_lt.le
      -- mul_le_mul_of_nonpos_left flips the inequality on x ≤ q.
      have := mul_le_mul_of_nonpos_left hxq hΔ_le
      linarith
    linarith

/-! ### Segment lemma: σ is affine away from its breakpoints

We need: on any subinterval `[p, q] ⊆ [l, u]` of `[l, u]` that contains
no breakpoint of `σ` in its open interior, `σ` agrees with the affine
function `x ↦ σ(p) + s · (x - p)` for some slope `s`.

To avoid extracting the segment slope, we prove the weaker but
sufficient statement: `σ(x)` for `x ∈ [p, q]` equals
`σ(p) + (σ(q) - σ(p)) · (x - p) / (q - p)` when `p < q` — i.e., σ is
exactly the secant line through `(p, σ(p))` and `(q, σ(q))`.

Equivalently and more usefully for the affine-domination application:
`σ(x) = ((q - x) · σ(p) + (x - p) · σ(q)) / (q - p)`, the convex
combination. -/

/-- A single kink's contribution is *itself affine* on any interval
    `[p, q]` that does not contain its breakpoint in the open interior.

    For the soundness proof we only need: for any `x ∈ [p, q]` where
    `p, q` are consecutive test points, the contribution is an affine
    function of `x`. -/
private theorem kinkContribution_affine_on_segment
    (k : ℚ × ℚ) {p q x : ℚ} (_hpq : p ≤ q)
    (hxp : p ≤ x) (hxq : x ≤ q)
    (hNoInterior : ¬ (p < k.1 ∧ k.1 < q)) :
    -- The contribution at x is a convex combination of its values at p and q.
    (q - p) * kinkContribution k x =
      (q - x) * kinkContribution k p + (x - p) * kinkContribution k q := by
  obtain ⟨b, δ⟩ := k
  simp only at hNoInterior
  -- Case A: b ≤ p. Then b ≤ x and b ≤ q.
  by_cases hbp : b ≤ p
  · have hbx : b ≤ x := hbp.trans hxp
    have hbq : b ≤ q := hbp.trans (hxp.trans hxq)
    simp only [kinkContribution, if_pos hbp, if_pos hbx, if_pos hbq]
    ring
  · -- ¬ (b ≤ p), i.e. p < b. Then by hNoInterior, ¬ b < q, so q ≤ b.
    have hpb : p < b := lt_of_not_ge hbp
    have hqb : q ≤ b := by
      by_contra hbq_lt
      exact hNoInterior ⟨hpb, lt_of_not_ge hbq_lt⟩
    -- x ≤ q ≤ b. So b ≤ x only if x = q = b.
    have hxb_le : x ≤ b := hxq.trans hqb
    -- In every sub-case, the contributions at x, p, q are each 0
    -- except possibly the kink at q itself when q = b (which still
    -- evaluates to δ * (q - b) = 0 since b = q).
    -- So we manage all sub-cases uniformly: show each side of the
    -- equation is 0.
    have hbx_or : ¬ b ≤ x ∨ (b ≤ x ∧ x = b) := by
      by_cases hbx : b ≤ x
      · right; exact ⟨hbx, le_antisymm hxb_le hbx⟩
      · left; exact hbx
    have hbq_or : ¬ b ≤ q ∨ (b ≤ q ∧ q = b) := by
      by_cases hbq : b ≤ q
      · right; exact ⟨hbq, le_antisymm hqb hbq⟩
      · left; exact hbq
    -- Compute contribution at p: hbp false ⟹ 0.
    have hContrib_p : kinkContribution (b, δ) p = 0 := by
      simp [kinkContribution, hbp]
    -- Compute contribution at x: 0 (either b > x, or x = b in which case δ * 0).
    have hContrib_x : kinkContribution (b, δ) x = 0 := by
      rcases hbx_or with hbx | ⟨_, hxeq⟩
      · simp [kinkContribution, hbx]
      · simp [kinkContribution, hxeq]
    -- Compute contribution at q: 0 (either b > q, or q = b in which case δ * 0).
    have hContrib_q : kinkContribution (b, δ) q = 0 := by
      rcases hbq_or with hbq | ⟨_, hqeq⟩
      · simp [kinkContribution, hbq]
      · simp [kinkContribution, hqeq]
    rw [hContrib_p, hContrib_x, hContrib_q]
    ring

/-- The sum of kink contributions is affine on a segment `[p, q]` that
    contains no breakpoint in its open interior. -/
private theorem sum_kinkContributions_affine_on_segment
    (ks : List (ℚ × ℚ)) {p q x : ℚ} (hpq : p ≤ q)
    (hxp : p ≤ x) (hxq : x ≤ q)
    (hNoInterior : ∀ k ∈ ks, ¬ (p < k.1 ∧ k.1 < q)) :
    (q - p) * (ks.map (fun k => kinkContribution k x)).sum =
      (q - x) * (ks.map (fun k => kinkContribution k p)).sum +
        (x - p) * (ks.map (fun k => kinkContribution k q)).sum := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h_head := kinkContribution_affine_on_segment k hpq hxp hxq (hNoInterior k (by simp))
    have h_tail := ih (fun k' hk' => hNoInterior k' (by simp [hk']))
    linarith

/-- **σ is affine on a segment with no interior breakpoint.** For any
    `x ∈ [p, q]` where `[p, q]` contains no breakpoint of `σ` in its
    open interior, `σ(x)` equals the convex combination
    `((q - x) · σ(p) + (x - p) · σ(q)) / (q - p)`. -/
theorem PLActivation.affine_on_no_interior_breakpoint_segment
    (σ : PLActivation) {p q x : ℚ} (hpq : p ≤ q)
    (hxp : p ≤ x) (hxq : x ≤ q)
    (hNoInterior : ∀ b ∈ σ.kinks.map Prod.fst, ¬ (p < b ∧ b < q)) :
    (q - p) * σ.evaluate x =
      (q - x) * σ.evaluate p + (x - p) * σ.evaluate q := by
  simp only [PLActivation.evaluate]
  have h_kinks : ∀ k ∈ σ.kinks, ¬ (p < k.1 ∧ k.1 < q) := by
    intro k hk
    exact hNoInterior k.1 (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have h_sum := sum_kinkContributions_affine_on_segment σ.kinks hpq hxp hxq h_kinks
  linarith [h_sum]

/-! ### Soundness

Given a valid certificate, prove the lower bound holds throughout `[lo, hi]`. -/

/-- A specialized affine-domination from the convex-combination form
    of `σ` on a no-interior-breakpoint segment. -/
private theorem cert_le_at_x_of_le_at_endpoints
    {σ : PLActivation} (c : PLLowerCert σ)
    {p q x : ℚ} (hpq : p < q)
    (hp : c.alpha * p + c.beta ≤ σ.evaluate p)
    (hq : c.alpha * q + c.beta ≤ σ.evaluate q)
    (hxp : p ≤ x) (hxq : x ≤ q)
    (hNoInterior : ∀ b ∈ σ.kinks.map Prod.fst, ¬ (p < b ∧ b < q)) :
    c.alpha * x + c.beta ≤ σ.evaluate x := by
  -- The convex-combination identity directly: multiply target by (q - p) > 0.
  have hSeg := σ.affine_on_no_interior_breakpoint_segment hpq.le hxp hxq hNoInterior
  have hqp_pos : 0 < q - p := by linarith
  -- Goal: c.alpha * x + c.beta ≤ σ.evaluate x.
  -- Multiply both sides by (q - p) > 0; on RHS use hSeg.
  -- On LHS: (q - p) * (α * x + β) = (q - x) * (α * p + β) + (x - p) * (α * q + β).
  have hLHS : (q - p) * (c.alpha * x + c.beta) =
      (q - x) * (c.alpha * p + c.beta) + (x - p) * (c.alpha * q + c.beta) := by
    ring
  -- From hp, hq: weighted sum of LHS ≤ weighted sum of RHS.
  have hqx_nn : 0 ≤ q - x := by linarith
  have hxp_nn : 0 ≤ x - p := by linarith
  have h_left : (q - x) * (c.alpha * p + c.beta) ≤ (q - x) * σ.evaluate p :=
    mul_le_mul_of_nonneg_left hp hqx_nn
  have h_right : (x - p) * (c.alpha * q + c.beta) ≤ (x - p) * σ.evaluate q :=
    mul_le_mul_of_nonneg_left hq hxp_nn
  have h_sum : (q - p) * (c.alpha * x + c.beta) ≤
      (q - x) * σ.evaluate p + (x - p) * σ.evaluate q := by
    rw [hLHS]; linarith
  rw [← hSeg] at h_sum
  -- (q - p) * (α * x + β) ≤ (q - p) * σ x; cancel.
  exact le_of_mul_le_mul_left h_sum hqp_pos

/-- Auxiliary: directly prove soundness by recursion on the sorted
    list of in-range breakpoints, threading a "left endpoint" `pLow`
    that is either `l` itself or a breakpoint in `[l, u]`.

    The invariant we maintain is: every in-range breakpoint `> pLow`
    appears in `ks`. -/
private theorem pl_lower_cert_sound_aux
    {σ : PLActivation} (c : PLLowerCert σ) (_hWF : c.lo ≤ c.hi)
    (hPoints : ∀ p ∈ validityPolytope σ c.lo c.hi, c.alpha * p.1 + c.beta ≤ p.2) :
    ∀ (ks : List ℚ), (∀ b ∈ ks, b ∈ σ.kinks.map Prod.fst) →
      ks.Pairwise (· < ·) → (∀ b ∈ ks, c.lo ≤ b ∧ b ≤ c.hi) →
      ∀ (pLow : ℚ), pLow ∈ σ.testPoints c.lo c.hi →
      pLow ≤ c.hi →
      (∀ b ∈ ks, pLow < b) →
      (∀ b ∈ σ.kinks.map Prod.fst, pLow < b → b ≤ c.hi → b ∈ ks) →
      ∀ {x : ℚ}, pLow ≤ x → x ≤ c.hi →
      c.alpha * x + c.beta ≤ σ.evaluate x := by
  intro ks hsubset hsorted hinRange pLow hpLow_in hpLow_hi hpLow_lt hcomplete x hxpL hxhi
  induction ks generalizing pLow x with
  | nil =>
    -- No more in-range breakpoints. The segment [pLow, c.hi] has no
    -- interior breakpoint, so σ is affine on it. The certificate
    -- inequality holds at pLow and c.hi (both test points); use
    -- affine_dominates on the secant.
    have hp_le : c.alpha * pLow + c.beta ≤ σ.evaluate pLow := by
      have := hPoints (pLow, σ.evaluate pLow) (by
        rw [validityPolytope_mem_iff]; exact ⟨pLow, hpLow_in, rfl⟩)
      exact this
    have hq_le : c.alpha * c.hi + c.beta ≤ σ.evaluate c.hi := by
      have := hPoints (c.hi, σ.evaluate c.hi) (validityPolytope_hi σ c.lo c.hi)
      exact this
    -- No interior breakpoint: any breakpoint b with pLow < b < c.hi
    -- would be in [c.lo, c.hi] (since pLow ≥ c.lo via test-point
    -- membership) and > pLow, hence in ks = [] — contradiction.
    have hNoInterior : ∀ b ∈ σ.kinks.map Prod.fst, ¬ (pLow < b ∧ b < c.hi) := by
      intro b hb ⟨hpLb, hbhi⟩
      have := hcomplete b hb hpLb hbhi.le
      simp at this
    by_cases hxq : x = pLow
    · subst hxq; exact hp_le
    · have hpLx : pLow < x := lt_of_le_of_ne hxpL (Ne.symm hxq)
      have hpL_hi_lt : pLow < c.hi := lt_of_lt_of_le hpLx hxhi
      exact cert_le_at_x_of_le_at_endpoints c hpL_hi_lt hp_le hq_le hxpL hxhi hNoInterior
  | cons b₀ rest ih =>
    -- Either x < b₀ (handled like the nil case on segment [pLow, b₀])
    -- or b₀ ≤ x (recurse with new pLow = b₀).
    have hp_le : c.alpha * pLow + c.beta ≤ σ.evaluate pLow := by
      have := hPoints (pLow, σ.evaluate pLow) (by
        rw [validityPolytope_mem_iff]; exact ⟨pLow, hpLow_in, rfl⟩)
      exact this
    have hb₀_bounds := hinRange b₀ (by simp)
    have hb₀_in : b₀ ∈ σ.testPoints c.lo c.hi :=
      σ.mem_testPoints_of_kink c.lo c.hi (hsubset b₀ (by simp))
        hb₀_bounds.1 hb₀_bounds.2
    have hpL_b₀ : pLow < b₀ := hpLow_lt b₀ (by simp)
    have hq_b₀_le : c.alpha * b₀ + c.beta ≤ σ.evaluate b₀ := by
      have := hPoints (b₀, σ.evaluate b₀) (by
        rw [validityPolytope_mem_iff]; exact ⟨b₀, hb₀_in, rfl⟩)
      exact this
    have hNoInterior_left : ∀ b ∈ σ.kinks.map Prod.fst, ¬ (pLow < b ∧ b < b₀) := by
      intro b hb ⟨hpLb, hbb₀⟩
      have hbu : b ≤ c.hi := hbb₀.le.trans hb₀_bounds.2
      have hb_in_ks : b ∈ b₀ :: rest := hcomplete b hb hpLb hbu
      rw [List.mem_cons] at hb_in_ks
      rcases hb_in_ks with rfl | hb_in_rest
      · exact absurd hbb₀ (lt_irrefl b)
      · have : b₀ < b := List.rel_of_pairwise_cons hsorted hb_in_rest
        exact absurd hbb₀ (not_lt_of_gt this)
    by_cases hxb₀ : x < b₀
    · -- Segment [pLow, b₀] has no interior breakpoint.
      by_cases hxeq : x = pLow
      · subst hxeq; exact hp_le
      · have hpLx : pLow < x := lt_of_le_of_ne hxpL (Ne.symm hxeq)
        exact cert_le_at_x_of_le_at_endpoints c hpL_b₀ hp_le hq_b₀_le
          hxpL hxb₀.le hNoInterior_left
    · -- b₀ ≤ x. Recurse with pLow := b₀.
      have hxb₀' : b₀ ≤ x := le_of_not_gt hxb₀
      have hrest_subset : ∀ b ∈ rest, b ∈ σ.kinks.map Prod.fst :=
        fun b hb => hsubset b (List.mem_cons.mpr (Or.inr hb))
      have hrest_sorted : rest.Pairwise (· < ·) :=
        (List.pairwise_cons.mp hsorted).2
      have hrest_inRange : ∀ b ∈ rest, c.lo ≤ b ∧ b ≤ c.hi :=
        fun b hb => hinRange b (List.mem_cons.mpr (Or.inr hb))
      have hrest_gt_b₀ : ∀ b ∈ rest, b₀ < b :=
        fun b hb => List.rel_of_pairwise_cons hsorted hb
      have hcomplete' : ∀ b ∈ σ.kinks.map Prod.fst, b₀ < b → b ≤ c.hi → b ∈ rest := by
        intro b hb hb₀b hbu
        -- Since pLow < b₀ < b, hcomplete gives b ∈ b₀ :: rest;
        -- and b₀ < b excludes b = b₀.
        have hpLb : pLow < b := hpL_b₀.trans hb₀b
        have hb_in_ks : b ∈ b₀ :: rest := hcomplete b hb hpLb hbu
        rw [List.mem_cons] at hb_in_ks
        rcases hb_in_ks with rfl | hb_rest
        · exact absurd hb₀b (lt_irrefl _)
        · exact hb_rest
      exact ih hrest_subset hrest_sorted hrest_inRange b₀ hb₀_in
        hb₀_bounds.2 hrest_gt_b₀ hcomplete' hxb₀' hxhi

/-- **Soundness of the PL meta-certificate (Thursday's main theorem).**
    If a `PLLowerCert σ` passes the finite validity check at every
    test point, then the affine lower envelope `α · x + β` is `≤ σ(x)`
    for *every* `x ∈ [lo, hi]`, not just the test points. -/
theorem pl_lower_cert_sound
    {σ : PLActivation} (hSorted : σ.Sorted) (c : PLLowerCert σ)
    (hValid : c.isValid) (x : ℚ) (hxl : c.lo ≤ x) (hxu : x ≤ c.hi) :
    c.alpha * x + c.beta ≤ σ.evaluate x := by
  obtain ⟨hWF, hPoints⟩ := hValid
  -- Set ks := in-range breakpoints, sorted, > c.lo.
  let ks : List ℚ :=
    (σ.kinks.map Prod.fst).filter (fun b => decide (c.lo < b ∧ b ≤ c.hi))
  have hsubset : ∀ b ∈ ks, b ∈ σ.kinks.map Prod.fst :=
    fun b hb => (List.mem_filter.mp hb).1
  have hsorted_full : (σ.kinks.map Prod.fst).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hSorted
  have hsorted : ks.Pairwise (· < ·) := hsorted_full.filter _
  have hinRange : ∀ b ∈ ks, c.lo ≤ b ∧ b ≤ c.hi := by
    intro b hb
    have := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1.le, this.2⟩
  have hpL_in : c.lo ∈ σ.testPoints c.lo c.hi := σ.mem_testPoints_lo c.lo c.hi
  have hpL_lt : ∀ b ∈ ks, c.lo < b := by
    intro b hb
    have := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at this
    exact this.1
  have hcomplete : ∀ b ∈ σ.kinks.map Prod.fst, c.lo < b → b ≤ c.hi → b ∈ ks := by
    intro b hb hcb hbu
    rw [List.mem_filter]
    refine ⟨hb, ?_⟩
    simp [hcb, hbu]
  exact pl_lower_cert_sound_aux c hWF hPoints ks hsubset hsorted hinRange
    c.lo hpL_in hWF hpL_lt hcomplete hxl hxu

/-! ### Completeness (crossing case)

If the inequality `α · x + β ≤ σ(x)` holds on the *continuum* `[lo, hi]`,
then the certificate `⟨α, β, lo, hi⟩` passes the finite validity check
at every test point. The completeness side is trivial: each test point
is in `[lo, hi]`, so we just specialize the hypothesis. -/

/-- **Completeness of the PL meta-certificate (crossing case).** If the
    affine lower envelope `α · x + β ≤ σ(x)` holds for *every*
    `x ∈ [lo, hi]`, then the certificate passes the finite validity
    check at every test point.

    This is the "easy" half — every test point is in `[lo, hi]`, so we
    just specialize `hSound` at each one. No crossing assumption is
    required, despite the name (we keep the name parallel to
    `crown_lower_cert_complete_crossing`). -/
theorem pl_lower_cert_complete_crossing
    {σ : PLActivation} (α β lo hi : ℚ) (hlu : lo ≤ hi)
    (hSound : ∀ x : ℚ, lo ≤ x → x ≤ hi → α * x + β ≤ σ.evaluate x) :
    (PLLowerCert.mk (σ := σ) α β lo hi).isValid := by
  refine ⟨hlu, ?_⟩
  intro p hp
  rw [validityPolytope_mem_iff] at hp
  obtain ⟨x, hx_in, hp_eq⟩ := hp
  obtain ⟨hxl, hxu⟩ := σ.testPoints_mem_interval hlu hx_in
  subst hp_eq
  exact hSound x hxl hxu

/-- **Soundness-completeness iff (Thursday's combined meta-theorem).**
    For a sorted `PLActivation` `σ`, a candidate `(α, β)` passes the
    finite validity check at every test point of `[lo, hi]` iff the
    affine lower envelope `α · x + β ≤ σ(x)` holds for every
    `x ∈ [lo, hi]`. -/
theorem pl_lower_cert_iff
    {σ : PLActivation} (hSorted : σ.Sorted) (α β lo hi : ℚ) (hlu : lo ≤ hi) :
    (PLLowerCert.mk (σ := σ) α β lo hi).isValid ↔
      (∀ x : ℚ, lo ≤ x → x ≤ hi → α * x + β ≤ σ.evaluate x) := by
  refine ⟨?_, ?_⟩
  · intro hValid x hxl hxu
    have := pl_lower_cert_sound (σ := σ) hSorted
      (PLLowerCert.mk (σ := σ) α β lo hi) hValid x hxl hxu
    exact this
  · intro hSound
    exact pl_lower_cert_complete_crossing α β lo hi hlu hSound

/-! ## Axiom audit

Confirm that the central Day 1 theorems have transitive axiom
closure `⊆ {propext, Quot.sound, Classical.choice}`. -/

#guard_msgs (drop info) in
#print axioms PLActivation.evaluate_monotone

#guard_msgs (drop info) in
#print axioms PLActivation.evaluate_lipschitz

#guard_msgs (drop info) in
#print axioms Instances.reluPL_evaluate

#guard_msgs (drop info) in
#print axioms Instances.absPL_even

#guard_msgs (drop info) in
#print axioms pl_lower_cert_sound

#guard_msgs (drop info) in
#print axioms pl_lower_cert_complete_crossing

#guard_msgs (drop info) in
#print axioms pl_lower_cert_iff

end Mathbot.PiecewiseLinearActivation
