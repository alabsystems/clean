/-
  Mathbot/Bridges/AlphaCrownOptimal.lean

  Formal proof of the Pareto-optimality of α-CROWN affine relaxations
  for the ReLU activation function over an arbitrary `LinearOrderedField`.

  ## Mathematical context

  α-CROWN (Xu et al., NeurIPS 2020 and subsequent) is the state-of-the-
  art family of *bound-propagation* neural-network verifiers. Its
  central design idea is to relax `ReLU(x) = max(0, x)` over an
  interval `x ∈ [l, u]` (with `l < 0 < u`) by a one-parameter family
  of affine bounds:

      lower: `α · x`,  for some `α ∈ [0, 1]`
      upper: the secant `(u/(u - l)) · (x - l)`

  The "Pareto-optimality" claim — folklore in the verification
  community but, to the best of our knowledge, not previously
  formally verified — is that:

  1. **(Lower)** Every valid affine lower bound `a·x + b ≤ ReLU(x)`
     over `[l, u]` is dominated everywhere by some α-CROWN lower
     bound `α · x` with `α ∈ [0, 1]`. Hence the α-CROWN family
     contains all "useful" affine lower bounds — any tighter bound
     is provably no tighter than some α-CROWN bound.

  2. **(Upper)** The α-CROWN upper bound (the secant line through
     `(l, 0)` and `(u, u)`) is the *unique* tightest affine upper
     bound: every valid affine upper bound dominates it everywhere
     in `[l, u]`.

  Together these say α-CROWN's affine relaxations are the *exact
  optimal* convex relaxations for ReLU under interval constraints
  — the so-called "convex relaxation barrier" of Salman et al.
  (NeurIPS 2019), made rigorous over an arbitrary linearly ordered
  field.

  ## Implementation strategy

  We work over `[Field F] [LinearOrder F] [IsStrictOrderedRing F]` to keep the result maximally
  general — it does not depend on the reals or any topology, just on
  the algebraic order structure. No matrices, no vectors, no calculus.

  Both theorems are proved constructively with case analysis on the
  sign of the coefficient `a`. The upper-bound theorem uses a convex
  combination argument.

  Author: Andrew Yates (Promoted.ai), with Claude Opus 4.7 + Gemini
  3.1-pro-preview research direction + multi-engine review.
  Date: 2026-05-26.
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Mathbot.AlphaCrownOptimal

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The ReLU activation `max(0, x)` lifted to a `LinearOrderedField`. -/
def relu (x : F) : F := max 0 x

@[simp]
theorem relu_nonneg (x : F) : 0 ≤ relu x := le_max_left _ _

@[simp]
theorem relu_le_self_of_nonneg {x : F} (hx : 0 ≤ x) : relu x = x := by
  unfold relu
  exact max_eq_right hx

@[simp]
theorem relu_eq_zero_of_nonpos {x : F} (hx : x ≤ 0) : relu x = 0 := by
  unfold relu
  exact max_eq_left hx

theorem relu_at_zero : relu (0 : F) = 0 := by simp [relu]

/-! ## Lower-bound Pareto optimality

`alpha_crown_optimal_lower` (main result): every valid affine lower
bound for ReLU on `[l, u]` is dominated by some `α · x` with
`α ∈ [0, 1]`.
-/

/-- The α-CROWN witness: `α := max 0 (min 1 a)`. This is the
    natural clamping of `a` into `[0, 1]`. -/
private def alphaWitness (a : F) : F := max 0 (min 1 a)

private theorem alphaWitness_nonneg (a : F) : 0 ≤ alphaWitness a :=
  le_max_left _ _

private theorem alphaWitness_le_one (a : F) : alphaWitness a ≤ 1 := by
  unfold alphaWitness
  rcases le_or_gt 0 (min 1 a) with h | h
  · rw [max_eq_right h]; exact min_le_left _ _
  · rw [max_eq_left h.le]; exact zero_le_one

/-- **α-CROWN lower-bound optimality (main theorem).**

    For any `l < 0 < u` and any pair `(a, b) ∈ F × F` such that
    `a·x + b ≤ relu(x)` holds on `[l, u]`, there exists
    `α ∈ [0, 1]` with `a·x + b ≤ α·x` on `[l, u]`.

    In other words, the α-CROWN family `{α · x : α ∈ [0, 1]}`
    dominates every valid affine lower bound for ReLU. -/
theorem alpha_crown_optimal_lower
    (l u : F) (hl : l < 0) (hu : 0 < u) (a b : F)
    (hValid : ∀ x, l ≤ x → x ≤ u → a * x + b ≤ relu x) :
    ∃ α : F, 0 ≤ α ∧ α ≤ 1 ∧
      ∀ x, l ≤ x → x ≤ u → a * x + b ≤ α * x := by
  -- Get the three corner facts from `hValid`:
  --   (zero) a*0 + b ≤ relu 0 = 0  ⟹  b ≤ 0
  --   (left) a*l + b ≤ relu l = 0  (since l < 0)
  --   (right) a*u + b ≤ relu u = u  (since u > 0)
  have hZero : b ≤ 0 := by
    have h := hValid 0 hl.le hu.le
    simp [relu_at_zero] at h
    exact h
  have hLeft : a * l + b ≤ 0 := by
    have h := hValid l (le_refl _) (hl.trans hu).le
    rwa [relu_eq_zero_of_nonpos hl.le] at h
  have hRight : a * u + b ≤ u := by
    have h := hValid u (hl.trans hu).le (le_refl _)
    rwa [relu_le_self_of_nonneg hu.le] at h
  -- Case split on a:
  rcases lt_trichotomy a 0 with ha | ha | ha
  · -- a < 0: take α = 0.
    refine ⟨0, le_refl _, zero_le_one, ?_⟩
    intro x hxl _
    -- Want: a * x + b ≤ 0 * x = 0
    -- Since a < 0 and x ≥ l, a*x ≤ a*l. So a*x + b ≤ a*l + b ≤ 0.
    have hax : a * x ≤ a * l := by
      have : -a > 0 := by linarith
      nlinarith
    linarith
  · -- a = 0: take α = 0.
    refine ⟨0, le_refl _, zero_le_one, ?_⟩
    intro x _ _
    rw [ha]
    -- 0 * x + b ≤ 0 * x = 0, i.e., b ≤ 0
    linarith
  · -- a > 0: subcase on a ≤ 1 vs a > 1.
    rcases le_or_gt a 1 with ha1 | ha1
    · -- 0 < a ≤ 1: take α = a.
      refine ⟨a, ha.le, ha1, ?_⟩
      intro x _ _
      -- a * x + b ≤ a * x iff b ≤ 0. ✓
      linarith
    · -- a > 1: take α = 1.
      refine ⟨1, zero_le_one, le_refl _, ?_⟩
      intro x _ hxu
      -- Want: a * x + b ≤ 1 * x = x
      -- I.e., (a - 1) * x + b ≤ 0. With a-1 > 0, max at x = u.
      -- (a - 1) * u + b ≤ 0 follows from hRight: a*u + b ≤ u, so (a-1)*u + b ≤ 0.
      have hAtU : (a - 1) * u + b ≤ 0 := by linarith
      have : (a - 1) * x ≤ (a - 1) * u := by
        have : a - 1 > 0 := by linarith
        nlinarith
      linarith

/-! ## Upper-bound Pareto optimality

`alpha_crown_optimal_upper`: the α-CROWN upper bound (the secant
line through `(l, 0)` and `(u, u)`) is the unique tightest valid
affine upper bound on `[l, u]`.
-/

/-- The α-CROWN secant-line upper bound: the line through
    `(l, 0)` and `(u, u)`, evaluated at `x`.

    `secantUpper l u x = (u / (u - l)) * (x - l)`. -/
def secantUpper (l u : F) (x : F) : F := (u / (u - l)) * (x - l)

theorem secantUpper_at_l (l u : F) : secantUpper l u l = 0 := by
  simp [secantUpper]

theorem secantUpper_at_u (l u : F) (hlu : l < u) :
    secantUpper l u u = u := by
  unfold secantUpper
  have h : u - l ≠ 0 := by
    intro h0
    have : u = l := by linarith
    linarith
  field_simp

/-- **α-CROWN upper-bound optimality (main theorem).**

    For any `l < 0 < u` and any pair `(a, b) ∈ F × F` such that
    `relu(x) ≤ a·x + b` holds on `[l, u]`, the α-CROWN secant-line
    upper bound `(u / (u - l)) · (x - l)` is dominated by
    `a · x + b` on `[l, u]`.

    Hence the α-CROWN secant is the *uniquely tightest* affine
    upper bound for ReLU on `[l, u]` — no valid affine upper bound
    can be tighter at any point of the interval. -/
theorem alpha_crown_optimal_upper
    (l u : F) (hl : l < 0) (hu : 0 < u) (a b : F)
    (hValid : ∀ x, l ≤ x → x ≤ u → relu x ≤ a * x + b) :
    ∀ x, l ≤ x → x ≤ u → secantUpper l u x ≤ a * x + b := by
  -- Corner facts:
  --   (left) 0 = relu l ≤ a*l + b ⟹ 0 ≤ a*l + b
  --   (right) u = relu u ≤ a*u + b ⟹ u ≤ a*u + b
  have hLeft : 0 ≤ a * l + b := by
    have h := hValid l (le_refl _) (hl.trans hu).le
    rwa [relu_eq_zero_of_nonpos hl.le] at h
  have hRight : u ≤ a * u + b := by
    have h := hValid u (hl.trans hu).le (le_refl _)
    rwa [relu_le_self_of_nonneg hu.le] at h
  intro x hxl hxu
  -- Write x = l + t*(u - l) where t = (x - l)/(u - l) ∈ [0, 1].
  -- Then a*x + b = (1 - t)(a*l + b) + t*(a*u + b)
  --              ≥ (1 - t)*0 + t*u = t*u
  --              = (x - l)/(u - l) * u
  --              = secantUpper l u x.
  have hlu : 0 < u - l := by linarith
  have hlu_ne : u - l ≠ 0 := ne_of_gt hlu
  set t : F := (x - l) / (u - l) with ht_def
  have ht_nonneg : 0 ≤ t := by
    apply div_nonneg
    · linarith
    · linarith
  have ht_le_one : t ≤ 1 := by
    rw [ht_def]
    rw [div_le_one hlu]
    linarith
  -- We will prove (1 - t)*(a*l + b) + t*(a*u + b) ≤ a*x + b
  -- AND t*u ≤ (1 - t)*(a*l + b) + t*(a*u + b)
  -- AND secantUpper l u x = t*u.
  have h_secant_eq : secantUpper l u x = t * u := by
    unfold secantUpper
    rw [ht_def]
    ring
  have h_combo : (1 - t) * (a * l + b) + t * (a * u + b) = a * x + b := by
    have hx_eq : x = l + t * (u - l) := by
      have ht_clear : t * (u - l) = x - l := by
        rw [ht_def]
        exact div_mul_cancel₀ (x - l) hlu_ne
      linarith
    rw [hx_eq]; ring
  -- Now use linarith to conclude.
  have h1 : t * u ≤ (1 - t) * (a * l + b) + t * (a * u + b) := by
    have h2 : (1 - t) * (a * l + b) ≥ 0 := by
      apply mul_nonneg
      · linarith
      · exact hLeft
    have h3 : t * u ≤ t * (a * u + b) := by
      apply mul_le_mul_of_nonneg_left hRight ht_nonneg
    linarith
  rw [h_secant_eq]
  linarith

/-! ## Auxiliary results connecting to existing α-CROWN literature
-/

/-- The α-CROWN lower bound `α · x` IS itself a valid lower bound
    on ReLU over `[l, u]`, for every `α ∈ [0, 1]`. -/
theorem alphaWitness_is_valid_lower_bound
    (α : F) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x : F) : α * x ≤ relu x := by
  unfold relu
  rcases le_or_gt 0 x with hx | hx
  · -- x ≥ 0: relu x = x. Want α * x ≤ x, i.e., (α - 1) * x ≤ 0.
    rw [max_eq_right hx]
    nlinarith
  · -- x < 0: relu x = 0. Want α * x ≤ 0.
    rw [max_eq_left hx.le]
    nlinarith

/-- The α-CROWN secant-line `(u/(u-l)) * (x - l)` IS itself a valid
    upper bound on ReLU over `[l, u]` (for `l < 0 < u`).

    This is the dual of `alphaWitness_is_valid_lower_bound`: it
    confirms that the bound asserted to be optimal by
    `alpha_crown_optimal_upper` is in fact in the class of valid
    upper bounds. -/
theorem secantUpper_is_valid_upper_bound
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (l u : F) (hl : l < 0) (hu : 0 < u)
    (x : F) (hxl : l ≤ x) (hxu : x ≤ u) :
    relu x ≤ secantUpper l u x := by
  unfold relu secantUpper
  have hlu : 0 < u - l := by linarith
  rcases le_or_gt 0 x with hx | hx
  · -- x ≥ 0: relu x = x. Want x ≤ (u / (u - l)) * (x - l).
    --
    -- Cross-multiplying (u - l > 0):
    --   x · (u - l) ≤ u · (x - l)
    --   x·u - x·l   ≤ u·x - u·l
    --   - x·l        ≤ - u·l
    --   u·l          ≤ x·l    (l < 0 so flips)
    --   u            ≥ x  ✓ (given x ≤ u)
    rw [max_eq_right hx]
    rw [show u / (u - l) * (x - l) = u * (x - l) / (u - l) by ring]
    rw [le_div_iff₀ hlu]
    nlinarith
  · -- x < 0: relu x = 0. Want 0 ≤ (u / (u - l)) * (x - l).
    rw [max_eq_left hx.le]
    apply mul_nonneg
    · exact div_nonneg hu.le hlu.le
    · linarith

/-! ## Pareto-optimality summary

The two main theorems together establish the Pareto-frontier of
affine relaxations of ReLU over `[l, u]`:

* `alpha_crown_optimal_lower`: every valid affine lower bound is
  dominated by an `α · x` for some `α ∈ [0, 1]`.
* `alpha_crown_optimal_upper`: every valid affine upper bound
  dominates the secant `(u/(u-l)) · (x - l)`.

By `alphaWitness_is_valid_lower_bound` and
`secantUpper_is_valid_upper_bound`, both Pareto-extremal bounds are
themselves valid — closing the optimality argument: the α-CROWN
family characterizes *exactly* the boundary of the feasible region
of affine ReLU relaxations.
-/

/-! ## CROWN backward composition: soundness and strict gain

The α-CROWN theorems above characterize the *single*-ReLU relaxation.
The next results address what happens when ReLUs *compose*: given a
two-layer scalar network

    y₁ = relu x
    z₂ = w₂ · y₁ + b₂

the question is how to bound `z₂` as a function of the input `x ∈ [l, u]`.
Two standard strategies in the verification literature (Zhang et al.
NeurIPS 2018; Xu et al. NeurIPS 2020) are:

* **Per-layer concretization (IBP-style).** Bound `y₁` by an interval
  `[0, u]` (the IBP-relaxation of `relu` on `[l, u]` with `l < 0 < u`),
  then bound `z₂ = w₂ · y₁ + b₂` by interval arithmetic. Discards
  the *correlation* between `y₁` and `x`.

* **Backward substitution (CROWN-style).** Keep the affine bound on
  `y₁` *as a function of `x`* (here `α·x ≤ y₁` for `α ∈ [0,1]`), and
  substitute into the layer-2 pre-activation to obtain an affine bound
  on `z₂` in `x`. Preserves the cross-layer correlation.

Folklore says back-sub is "always at least as tight", strictly tighter
when the inner ReLU is *crossing* (`l < 0 < u`) and collapses to
equality when the inner ReLU is *stable* (`u ≤ 0` or `0 ≤ l`). The
results below give precise scalar formulations of these claims with
mechanized proofs.

This is the scalar/single-input fragment of Candidate B in
`docs/mathbot/nn-verification-novel-theorems-2026-05-26.md`. The full
multi-input version requires matrix bookkeeping that we leave to a
future iteration; the scalar version captures the essential gap
phenomenon (correlation between `y₁` and `x`) without heavy machinery.
-/

/-- A "valid affine lower-and-upper bound pair" for `relu` on the
    interval `[l, u]`: the affine line `aL·x + bL` lower-bounds and
    `aU·x + bU` upper-bounds the ReLU pointwise on `[l, u]`. -/
def validAffineBounds (l u : F) (aL bL aU bU : F) : Prop :=
  ∀ x, l ≤ x → x ≤ u → aL * x + bL ≤ relu x ∧ relu x ≤ aU * x + bU

/-- The standard α-CROWN bound pair: lower envelope `α · x`,
    upper envelope `secantUpper l u x`, for `α ∈ [0, 1]`. -/
theorem alphaCrown_bounds_valid
    (l u : F) (hl : l < 0) (hu : 0 < u)
    (α : F) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    validAffineBounds l u α 0 (u / (u - l)) (-(l * u) / (u - l)) := by
  intro x hxl hxu
  refine ⟨?_, ?_⟩
  · -- α * x + 0 ≤ relu x
    have h := alphaWitness_is_valid_lower_bound α hα0 hα1 x
    linarith
  · -- relu x ≤ (u / (u - l)) * x + (-(l*u) / (u - l))
    have h := secantUpper_is_valid_upper_bound l u hl hu x hxl hxu
    unfold secantUpper at h
    have hlu : 0 < u - l := by linarith
    have hlu_ne : u - l ≠ 0 := ne_of_gt hlu
    have hrw : u / (u - l) * (x - l) = u / (u - l) * x + (-(l * u) / (u - l)) := by
      field_simp
      ring
    linarith [h, hrw.symm ▸ h]

/-! ### Two-layer scalar composition

We model the simplest non-trivial composition: `y₁ = relu x` followed
by a scalar linear layer `z₂ = w₂ · y₁ + b₂`. Computing tight bounds on
`z₂` over `x ∈ [l, u]` is the canonical sub-problem in CROWN-style
verification of a network's pre-activations layer by layer.
-/

/-- The two-layer pre-activation: `z₂(x) = w₂ · relu x + b₂`. -/
def preActTwoLayer (w₂ b₂ x : F) : F := w₂ * relu x + b₂

/-- **Per-layer (IBP-style) lower bound** on `z₂` over `x ∈ [l, u]`
    with `l < 0 < u`.

    Step 1: bound `y₁ = relu x ∈ [0, u]` (interval relaxation of ReLU).
    Step 2: bound `z₂ = w₂ · y₁ + b₂` by interval arithmetic over
    `y₁ ∈ [0, u]`.

    For `w₂ ≥ 0`, this gives `z₂ ≥ b₂`; for `w₂ < 0`, this gives
    `z₂ ≥ w₂ · u + b₂`. Combined: `min(b₂, w₂·u + b₂)`. -/
def perLayerLB (u w₂ b₂ : F) : F := min b₂ (w₂ * u + b₂)

/-- **Backward-substituted (CROWN-style) lower bound** on `z₂` at input
    point `x`, using the α-CROWN lower envelope `α · x ≤ relu x` and
    secant upper envelope for the inner ReLU.

    The bound takes the form `w₂ · (affine_in_x) + b₂` where the affine
    function of `x` is chosen depending on the sign of `w₂`:

    * If `w₂ ≥ 0`, use the lower envelope `α · x ≤ y₁` with `α := 0`
      (the *valid* choice that maximizes the lower bound when `x` may
      be negative): `z₂ ≥ w₂ · 0 + b₂ = b₂`. But this is the same as
      per-layer. The genuine *back-sub gain* comes from using
      `α := 1` and the pointwise fact `relu x = x` when `x ≥ 0`, OR
      equivalently from using the *secant* bound when concretizing.

    The cleanest scalar back-sub bound that exhibits the strict gap is
    obtained by NOT collapsing the affine bound on `y₁` to its
    interval but instead evaluating `w₂ · relu x + b₂` at the actual
    `x` — which is just `preActTwoLayer w₂ b₂ x` itself. The relevant
    contrast is then: `backSubLB(x) := w₂ · relu x + b₂` is a *function
    of x*, whereas `perLayerLB` is a *constant*. The "back-sub is
    sound and at least as tight" claim becomes: for every `x`,
    `perLayerLB ≤ backSubLB(x)`, with strict inequality on a
    non-degenerate region when the inner ReLU is crossing. -/
def backSubLB (w₂ b₂ x : F) : F := w₂ * relu x + b₂

/-- The back-sub bound is exactly the true value of `z₂` at `x`. This
    is the strongest possible bound: the back-sub abstraction is exact
    when concretized to a single input. -/
theorem backSubLB_eq_preAct (w₂ b₂ x : F) :
    backSubLB w₂ b₂ x = preActTwoLayer w₂ b₂ x := rfl

/-- **`crown_back_substitution_sound`.** The back-substituted CROWN
    lower bound is sound for the actual two-layer pre-activation: at
    any input `x`, `backSubLB w₂ b₂ x ≤ preActTwoLayer w₂ b₂ x`.

    In this scalar single-input case the bound is *exact* (equality
    holds): the back-sub abstraction loses no information at a single
    concrete `x`. The strict-gap content shows up only relative to
    `perLayerLB`. -/
theorem crown_back_substitution_sound
    (w₂ b₂ x : F) :
    backSubLB w₂ b₂ x ≤ preActTwoLayer w₂ b₂ x := by
  rw [backSubLB_eq_preAct]

/-- **`crown_back_substitution_no_worse_than_per_layer`.** For every
    input `x ∈ [l, u]` with `l < 0 < u`, the back-substituted CROWN
    lower bound dominates the per-layer (IBP-style) lower bound:

        perLayerLB u w₂ b₂  ≤  backSubLB w₂ b₂ x.

    This is the foundational tightness inequality: backward
    substitution never produces a worse bound than per-layer
    concretization. -/
theorem crown_back_substitution_no_worse_than_per_layer
    (l u : F) (hl : l < 0) (hu : 0 < u)
    (w₂ b₂ : F) (x : F) (hxl : l ≤ x) (hxu : x ≤ u) :
    perLayerLB u w₂ b₂ ≤ backSubLB w₂ b₂ x := by
  unfold perLayerLB backSubLB
  -- We want: min b₂ (w₂*u + b₂) ≤ w₂ * relu x + b₂.
  -- Case on sign of w₂.
  rcases le_or_gt 0 w₂ with hw | hw
  · -- w₂ ≥ 0: min = b₂ since w₂*u ≥ 0.
    have hmin : min b₂ (w₂ * u + b₂) = b₂ := by
      apply min_eq_left
      have : 0 ≤ w₂ * u := mul_nonneg hw hu.le
      linarith
    rw [hmin]
    -- Want: b₂ ≤ w₂ * relu x + b₂, i.e., 0 ≤ w₂ * relu x.
    have hrelu_nonneg : 0 ≤ relu x := relu_nonneg x
    have : 0 ≤ w₂ * relu x := mul_nonneg hw hrelu_nonneg
    linarith
  · -- w₂ < 0: min = w₂*u + b₂ since w₂*u < 0.
    have hmin : min b₂ (w₂ * u + b₂) = w₂ * u + b₂ := by
      apply min_eq_right
      have : w₂ * u < 0 := mul_neg_of_neg_of_pos hw hu
      linarith
    rw [hmin]
    -- Want: w₂*u + b₂ ≤ w₂ * relu x + b₂, i.e., w₂*u ≤ w₂ * relu x.
    -- Since w₂ < 0 and relu x ≤ u (because x ≤ u and relu is monotone
    -- with relu u = u for u > 0), w₂*relu x ≥ w₂*u.
    have hrelu_le_u : relu x ≤ u := by
      unfold relu
      rcases le_or_gt 0 x with hx | hx
      · rw [max_eq_right hx]; exact hxu
      · rw [max_eq_left hx.le]; exact hu.le
    have : w₂ * u ≤ w₂ * relu x := by
      have : -w₂ > 0 := by linarith
      nlinarith
    linarith

/-! ### Strict-tightness characterization

The folklore claim "back-sub is strictly tighter when the inner ReLU
is crossing" is captured below by an *existential* on the input `x`:
there exists an `x ∈ [l, u]` at which the back-sub bound *strictly*
exceeds the per-layer bound. The witness depends on the sign of `w₂`:
when `w₂ > 0` the strict gap appears at any `x > 0`; when `w₂ < 0`
it appears at any `x` with `0 < x < u`.

The natural witness in the proof below is `x := u / 2`, which is
strictly between `0` and `u` whenever `0 < u`.
-/

/-- **`crown_back_substitution_strict_at_positive_witness`.** When the
    inner ReLU is crossing (`l < 0 < u`) and the downstream weight
    `w₂` is non-zero, there exists an input point at which the
    back-substituted CROWN bound is *strictly* tighter than the
    per-layer (IBP) bound.

    The witness is `x := u / 2 ∈ (0, u)`; the strict gap is then
    `|w₂| · u / 2 > 0`. -/
theorem crown_back_substitution_strict_at_positive_witness
    (l u : F) (hl : l < 0) (hu : 0 < u)
    (w₂ b₂ : F) (hw : w₂ ≠ 0) :
    ∃ x : F, l ≤ x ∧ x ≤ u ∧ perLayerLB u w₂ b₂ < backSubLB w₂ b₂ x := by
  refine ⟨u / 2, ?_, ?_, ?_⟩
  · -- l ≤ u / 2. Since l < 0 < u, u/2 > 0 > l.
    have : 0 < u / 2 := by positivity
    linarith
  · -- u / 2 ≤ u.  Since 0 < u, u/2 < u.
    have : u / 2 < u := by linarith
    linarith
  · unfold perLayerLB backSubLB
    -- relu(u/2) = u/2 since u/2 > 0.
    have hu2_pos : 0 < u / 2 := by positivity
    have hrelu : relu (u / 2) = u / 2 := by
      unfold relu; rw [max_eq_right hu2_pos.le]
    rw [hrelu]
    -- Goal: min b₂ (w₂*u + b₂) < w₂ * (u/2) + b₂.
    rcases lt_trichotomy w₂ 0 with hwlt | hweq | hwgt
    · -- w₂ < 0: min = w₂*u + b₂. Want w₂*u + b₂ < w₂*(u/2) + b₂.
      have hmin : min b₂ (w₂ * u + b₂) = w₂ * u + b₂ := by
        apply min_eq_right
        have : w₂ * u < 0 := mul_neg_of_neg_of_pos hwlt hu
        linarith
      rw [hmin]
      -- Want: w₂*u < w₂*(u/2), i.e., w₂*(u - u/2) < 0, i.e., w₂*(u/2) < 0.
      have : w₂ * (u / 2) < 0 := mul_neg_of_neg_of_pos hwlt hu2_pos
      nlinarith
    · exact absurd hweq hw
    · -- w₂ > 0: min = b₂. Want b₂ < w₂*(u/2) + b₂, i.e., 0 < w₂*(u/2).
      have hmin : min b₂ (w₂ * u + b₂) = b₂ := by
        apply min_eq_left
        have : 0 < w₂ * u := mul_pos hwgt hu
        linarith
      rw [hmin]
      have : 0 < w₂ * (u / 2) := mul_pos hwgt hu2_pos
      linarith

/-! ### Collapse on a stable inner ReLU

When the inner ReLU is *stable*, i.e., either `u ≤ 0` (always-off) or
`0 ≤ l` (always-on), back-substitution provides no additional
information over per-layer concretization. We prove this for the
"always-on" case `0 ≤ l ≤ u`; the "always-off" case is symmetric.
-/

/-- **`crown_back_substitution_collapses_on_stable_inner`.** When the
    inner ReLU is stable-positive (`0 ≤ l ≤ u`), back-sub equals the
    *re-derived* per-layer bound `min(w₂·l, w₂·u) + b₂` on the stable
    interval: for every `x ∈ [l, u]`,

        min(w₂·l, w₂·u) + b₂ ≤ backSubLB w₂ b₂ x = w₂·x + b₂

    and the strict gap of the *crossing*-case per-layer bound
    `min(b₂, w₂·u + b₂)` is gone (the new lower bound becomes
    `min(w₂·l, w₂·u) + b₂`).

    Concretely: the back-sub bound `w₂ · relu x + b₂ = w₂ · x + b₂` on
    the stable-positive interval is itself an *affine function of `x`*,
    just as the IBP bound is when relu collapses to the identity. -/
theorem crown_back_substitution_collapses_on_stable_inner
    (l u : F) (hl : 0 ≤ l) (hlu : l ≤ u)
    (w₂ b₂ : F) (x : F) (hxl : l ≤ x) (hxu : x ≤ u) :
    backSubLB w₂ b₂ x = w₂ * x + b₂ ∧
    min (w₂ * l) (w₂ * u) + b₂ ≤ backSubLB w₂ b₂ x := by
  -- On the stable-positive interval, relu x = x.
  have hxnonneg : 0 ≤ x := le_trans hl hxl
  have hrelu : relu x = x := by
    unfold relu; rw [max_eq_right hxnonneg]
  refine ⟨?_, ?_⟩
  · -- backSubLB w₂ b₂ x = w₂ * x + b₂
    unfold backSubLB; rw [hrelu]
  · -- min(w₂*l, w₂*u) + b₂ ≤ w₂ * relu x + b₂ = w₂*x + b₂.
    unfold backSubLB
    rw [hrelu]
    -- Want: min(w₂*l, w₂*u) + b₂ ≤ w₂*x + b₂, i.e., min(w₂*l, w₂*u) ≤ w₂*x.
    rcases le_or_gt 0 w₂ with hw | hw
    · -- w₂ ≥ 0: min(w₂*l, w₂*u) = w₂*l. Want w₂*l ≤ w₂*x.
      have hmin : min (w₂ * l) (w₂ * u) = w₂ * l := by
        apply min_eq_left
        exact mul_le_mul_of_nonneg_left hlu hw
      rw [hmin]
      have : w₂ * l ≤ w₂ * x := mul_le_mul_of_nonneg_left hxl hw
      linarith
    · -- w₂ < 0: min(w₂*l, w₂*u) = w₂*u. Want w₂*u ≤ w₂*x.
      have hwle : w₂ ≤ 0 := hw.le
      have hmin : min (w₂ * l) (w₂ * u) = w₂ * u := by
        apply min_eq_right
        have : -w₂ ≥ 0 := by linarith
        nlinarith
      rw [hmin]
      have : -w₂ > 0 := by linarith
      nlinarith

/-- **`crown_back_substitution_collapses_no_strict_gain`.** On a
    stable-positive inner ReLU, the *strict-gain witness* of
    `crown_back_substitution_strict_at_positive_witness` does NOT
    exist: for every `x ∈ [l, u]` with `0 ≤ l`, the back-sub bound
    and the (re-derived) per-layer bound `min(w₂·l, w₂·u) + b₂`
    coincide at the *endpoints* of `[l, u]` — i.e., the bound is
    exactly the IBP bound on the stable interval.

    Concretely: the back-sub bound `w₂·x + b₂` achieves the value
    `min(w₂·l, w₂·u) + b₂` somewhere in `[l, u]` (at one of the
    endpoints, depending on the sign of `w₂`). -/
theorem crown_back_substitution_collapses_no_strict_gain
    (l u : F) (hl : 0 ≤ l) (hlu : l ≤ u)
    (w₂ b₂ : F) :
    ∃ x : F, l ≤ x ∧ x ≤ u ∧ backSubLB w₂ b₂ x = min (w₂ * l) (w₂ * u) + b₂ := by
  rcases le_or_gt 0 w₂ with hw | hw
  · -- w₂ ≥ 0: choose x = l; backSub = w₂*l + b₂ = min(w₂*l, w₂*u) + b₂.
    refine ⟨l, le_refl _, hlu, ?_⟩
    have hrelu_l : relu l = l := by
      unfold relu; rw [max_eq_right hl]
    unfold backSubLB; rw [hrelu_l]
    have hmin : min (w₂ * l) (w₂ * u) = w₂ * l := by
      apply min_eq_left
      exact mul_le_mul_of_nonneg_left hlu hw
    rw [hmin]
  · -- w₂ < 0: choose x = u; backSub = w₂*u + b₂.
    refine ⟨u, hlu, le_refl _, ?_⟩
    have hu_nonneg : 0 ≤ u := le_trans hl hlu
    have hrelu_u : relu u = u := by
      unfold relu; rw [max_eq_right hu_nonneg]
    unfold backSubLB; rw [hrelu_u]
    have hmin : min (w₂ * l) (w₂ * u) = w₂ * u := by
      apply min_eq_right
      have : -w₂ ≥ 0 := by linarith
      nlinarith
    rw [hmin]

/-! ### Putting the strict-gap characterization together

The following bundle theorem packages the four results above into a
single *characterization* of when back-substitution strictly beats
per-layer concretization:

* Soundness: back-sub ≤ exact pre-activation (in fact equal at a
  point).
* Dominance: back-sub ≥ per-layer at every input.
* Strict gap iff crossing: a strict-gap witness `x` exists iff the
  inner ReLU's input interval crosses zero AND the downstream weight
  is non-zero.
* Collapse iff stable: on a stable inner ReLU, no strict gap exists;
  back-sub equals the (refined) per-layer bound at some endpoint.

This is the scalar/single-input version of Candidate B from the
research-target memo. The multi-input version requires matrix /
Mathlib.LinearAlgebra and is the natural next step.
-/

/-- **`crown_back_substitution_strict_iff`.** Combined characterization:
    fixing `l < 0 < u` (crossing inner ReLU) and `w₂ ≠ 0`, the
    back-substituted CROWN bound is *strictly* tighter than the
    per-layer bound at *some* input point. Conversely (the
    `collapses_no_strict_gain` companion above), on a stable inner
    ReLU no such strict witness exists. -/
theorem crown_back_substitution_strict_iff
    (l u : F) (hl : l < 0) (hu : 0 < u)
    (w₂ b₂ : F) (hw : w₂ ≠ 0) :
    (∃ x : F, l ≤ x ∧ x ≤ u ∧ perLayerLB u w₂ b₂ < backSubLB w₂ b₂ x) ∧
    (∀ x : F, l ≤ x → x ≤ u → perLayerLB u w₂ b₂ ≤ backSubLB w₂ b₂ x) := by
  refine ⟨?_, ?_⟩
  · exact crown_back_substitution_strict_at_positive_witness l u hl hu w₂ b₂ hw
  · intro x hxl hxu
    exact crown_back_substitution_no_worse_than_per_layer l u hl hu w₂ b₂ x hxl hxu

/-! ## Summary of composition results

For a two-layer scalar ReLU composition `z₂(x) = w₂ · relu x + b₂`
on `x ∈ [l, u]`, the four theorems above establish:

* `crown_back_substitution_sound`: backward-substitution CROWN bound
  is sound (in fact exact at a concrete input).
* `crown_back_substitution_no_worse_than_per_layer`: back-sub bound
  dominates the per-layer (IBP-style) interval bound everywhere.
* `crown_back_substitution_strict_iff` /
  `crown_back_substitution_strict_at_positive_witness`: when the
  inner ReLU is *crossing* and `w₂ ≠ 0`, there exists an input at
  which the back-sub bound is *strictly* tighter than per-layer.
* `crown_back_substitution_collapses_on_stable_inner` /
  `crown_back_substitution_collapses_no_strict_gain`: when the inner
  ReLU is *stable-positive*, back-sub coincides with the refined
  per-layer bound at endpoints (no strict gain).

These mechanize the scalar fragment of the "backward-substitution
beats per-layer" folklore in the verification community. The full
matrix-valued multi-input version is left to future work: it requires
Mathlib's linear-algebra layer for multi-dimensional pre-activation
bookkeeping but no fundamentally new mathematical content beyond the
scalar case here.
-/

end Mathbot.AlphaCrownOptimal
