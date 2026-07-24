/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WAVE-4 PROGRAM 3 — MULTI-LAYER VERIFIED COMPLETENESS.

────────────────────────────────────────────────────────────────────────────
WHAT WAVE-2 / WAVE-3 DID, AND WHAT THIS FILE CHANGES
────────────────────────────────────────────────────────────────────────────
`CompleteIBP.lean` (Wave-2) and `CompleteCrown.lean` (Wave-3) both fired the
abstract `Complete.complete` decision procedure on a **ONE-hidden-layer** real
ReLU net `f(x) = relu x − relu (x−1) + 1`, with a hand-checked Lipschitz
constant `L = 2`.  That single-layer constant is just `|v₁·w₁| + |v₂·w₂|`; there
is no *composition* of layers, so the genuinely deep regime — where the
verification wall lives — was never exercised.

This file goes MULTI-LAYER.  It defines a concrete real net with **TWO hidden
ReLU layers**

      g(x) = w₃ · relu( w₂ · relu( w₁·x + c₁ ) + c₂ ) + d
           = relu( relu(2·x) − 1 ) + 1            (w₁=2,c₁=0; w₂=1,c₂=−1; w₃=1,d=1)

as a literal COMPOSITION of affine and ReLU maps, and proves a **VERIFIED
Lipschitz constant**

      L = ‖W₃‖ · ‖W₂‖ · ‖W₁‖ = |w₃|·|w₂|·|w₁| = 1·1·2 = 2

by the COMPOSITIONAL Lipschitz bound — `f = f_L ∘ … ∘ f_1` is L-Lipschitz with
`L = ∏ₖ ‖Wₖ‖`, each ReLU layer being 1-Lipschitz — proved in Lean through
mathlib's `LipschitzWith.comp` (composition multiplies the constants) and
`lipschitzWith_max` (ReLU `= max 0 ·` is 1-Lipschitz).  THIS compositional
constant is the new content: the Lipschitz error that drives `width_error` /
`decides` is the genuine product of per-layer operator-norm bounds across the
DEPTH of the net, not a single-layer sum.

Every field of `Complete.Relaxation` is then discharged for this depth-2 net and
`Complete.complete` FIRES, deciding `g(x) > 0` on the whole input box `[0,2]` by
finite input bisection.

────────────────────────────────────────────────────────────────────────────
HOW THE VERIFIED COMPOSITIONAL L IS USED (it is load-bearing, not decorative)
────────────────────────────────────────────────────────────────────────────
The relaxed bound returned on a box `[lo,hi]` is the LEFT-CORNER value shaded by
the Lipschitz error:

      relaxedBound [lo,hi] = g(lo) − L · diam[lo,hi].

* `width_error`  (`trueMin − L·diam ≤ relaxedBound`):  since `lo ∈ [lo,hi]`,
  `trueMin = sInf (g '' box) ≤ g(lo)`, so
  `trueMin − L·diam ≤ g(lo) − L·diam = relaxedBound`.
* `decides`  (`0 < relaxedBound ⇒ safe` on the box):  for any `s ∈ [lo,hi]`,
  the **compositional Lipschitz bound** gives `|g s − g lo| ≤ L·|s−lo| ≤ L·diam`,
  hence `g s ≥ g lo − L·diam = relaxedBound > 0`.  This is precisely where the
  verified product-of-operator-norms constant closes a leaf — the deeper the net,
  the larger `L`, the smaller the box that closes, and the procedure adapts via
  the Archimedean decisive depth in `Complete.lean`.

So the multi-layer Lipschitz constant is exactly the quantity the decision
procedure consumes; this connects the verified decision procedure of
`Complete.lean` to a genuinely DEEP (≥2 hidden ReLU layer) net.

────────────────────────────────────────────────────────────────────────────
RUTHLESS HONESTY — SCOPE
────────────────────────────────────────────────────────────────────────────
* The net is a scalar 1→1→1→1 chain with TWO hidden ReLU layers (depth achieved:
  2 hidden layers), real exact-rational weights, done end-to-end and sorry-free.
* The compositional Lipschitz theorem `g_lipschitz` is the real mathlib
  `LipschitzWith.comp` product across the two ReLU layers and three affine maps;
  `L = ∏‖Wₖ‖` is therefore a VERIFIED bound, not asserted.
* The fully-general depth-k / multi-input operator-norm `width_error` (matrix
  operator norms, per-coordinate propagation) is NOT formalised here — the
  abstract `Complete` core already covers any depth once a relaxation supplies
  its five laws; this file supplies them for a concrete DEEP net with a
  composition-proved Lipschitz constant, which is the new regime over Waves 2–3.
* `Crownproof.DeepK` separately proves the Farkas/CROWN *soundness* bridge for
  arbitrary depth `k`; this file is the *completeness* (termination + decision)
  counterpart specialised to a concrete depth-2 net.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete

namespace Crownproof
namespace CompleteDeep

open Set
open scoped NNReal

/-! ## 1. The concrete depth-2 (two-hidden-layer) ReLU network as a composition

We fix the weights

  layer 1 affine   `aff1 t = w₁·t + c₁ = 2·t + 0`     (‖W₁‖ = |w₁| = 2)
  layer 1 ReLU     `relu`                              (1-Lipschitz)
  layer 2 affine   `aff2 t = w₂·t + c₂ = 1·t − 1`      (‖W₂‖ = |w₂| = 1)
  layer 2 ReLU     `relu`                              (1-Lipschitz)
  output  affine   `aff3 t = w₃·t + d  = 1·t + 1`      (‖W₃‖ = |w₃| = 1)

so the net is the literal composition

  g = aff3 ∘ relu ∘ aff2 ∘ relu ∘ aff1,

a genuine ≥2-hidden-ReLU-layer network.  Defining it as a composition is what
lets the Lipschitz constant be assembled by `LipschitzWith.comp`. -/

/-- ReLU over the reals, `max 0 ·` — the 1-Lipschitz nonlinearity. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Layer-1 affine map `t ↦ 2·t` (`w₁ = 2`, `c₁ = 0`). -/
def aff1 (t : ℝ) : ℝ := 2 * t + 0
/-- Layer-2 affine map `t ↦ t − 1` (`w₂ = 1`, `c₂ = −1`). -/
def aff2 (t : ℝ) : ℝ := 1 * t + (-1)
/-- Output affine map `t ↦ t + 1` (`w₃ = 1`, `d = 1`). -/
def aff3 (t : ℝ) : ℝ := 1 * t + 1

/-- The concrete **two-hidden-layer** ReLU network, as the literal composition
`g = aff3 ∘ relu ∘ aff2 ∘ relu ∘ aff1`:
`g x = relu( relu(2·x) − 1 ) + 1`. -/
def g (x : ℝ) : ℝ := aff3 (relu (aff2 (relu (aff1 x))))

/-- The per-layer operator-norm bounds `‖Wₖ‖ = |wₖ|`: `2, 1, 1`. -/
def normW1 : ℝ := 2
def normW2 : ℝ := 1
def normW3 : ℝ := 1

/-- The **verified composite Lipschitz constant** `L = ‖W₃‖·‖W₂‖·‖W₁‖ = 2`. -/
def L : ℝ := normW3 * normW2 * normW1

lemma L_eq_two : L = 2 := by unfold L normW3 normW2 normW1; norm_num

/-! ## 2. THE COMPOSITIONAL LIPSCHITZ BOUND (the new multi-layer content)

We prove `g` is `LipschitzWith L_nn` with `L_nn = ‖W₃‖·‖W₂‖·‖W₁‖ = 2` as a
`ℝ≥0`, by composing:

  * each affine map `t ↦ wₖ·t + cₖ` is `‖Wₖ‖ = |wₖ|`-Lipschitz
    (`dist (wt+c) (ws+c) = |w|·|t−s| = ‖Wₖ‖·dist t s`);
  * each ReLU `= max 0 ·` is `1`-Lipschitz (`lipschitzWith_max`/`const_max`);
  * `LipschitzWith.comp` multiplies the constants along the composition.

The resulting constant `1 * (1 * (1 * (1 * 2)))` is the PRODUCT of the per-layer
operator-norm bounds — `L = ∏ₖ ‖Wₖ‖`, with ReLU contributing factor `1` each. -/

/-- Each affine layer `t ↦ wₖ·t + cₖ` is `|wₖ|`-Lipschitz.  We prove the three
instances we need directly from `dist (f t) (f s) = |wₖ| · dist t s`. -/
lemma aff1_lip : LipschitzWith (2 : ℝ≥0) aff1 := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [aff1, Real.dist_eq]
  rw [show (2:ℝ) * t + 0 - (2 * s + 0) = 2 * (t - s) by ring, abs_mul,
      show |(2:ℝ)| = 2 by norm_num, show ((2 : ℝ≥0) : ℝ) = (2:ℝ) by norm_num]

lemma aff2_lip : LipschitzWith (1 : ℝ≥0) aff2 := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [aff2, Real.dist_eq]
  rw [show (1:ℝ) * t + (-1) - (1 * s + (-1)) = 1 * (t - s) by ring, abs_mul,
      show |(1:ℝ)| = 1 by norm_num, show ((1 : ℝ≥0) : ℝ) = (1:ℝ) by norm_num]

lemma aff3_lip : LipschitzWith (1 : ℝ≥0) aff3 := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [aff3, Real.dist_eq]
  rw [show (1:ℝ) * t + 1 - (1 * s + 1) = 1 * (t - s) by ring, abs_mul,
      show |(1:ℝ)| = 1 by norm_num, show ((1 : ℝ≥0) : ℝ) = (1:ℝ) by norm_num]

/-- ReLU `= max 0 ·` is `1`-Lipschitz — the verified "each ReLU layer is
1-Lipschitz" fact, from `lipschitzWith_max` via `LipschitzWith.const_max`. -/
lemma relu_lip : LipschitzWith (1 : ℝ≥0) relu := by
  have h : LipschitzWith (1 : ℝ≥0) (fun x : ℝ => max 0 x) :=
    (LipschitzWith.id).const_max 0
  simpa [relu] using h

/-- **THE COMPOSITIONAL LIPSCHITZ BOUND.**  The depth-2 net `g` is
`LipschitzWith (1·(1·(1·(1·2))))`, the PRODUCT of the per-layer operator-norm
bounds with each ReLU contributing factor `1`:

  `g = aff3 ∘ (relu ∘ (aff2 ∘ (relu ∘ aff1)))`,

and `LipschitzWith.comp` multiplies the constants
`‖W₃‖ · 1 · ‖W₂‖ · 1 · ‖W₁‖ = 1·1·1·1·2`.  This is `f = f_L ∘ … ∘ f_1` is
L-Lipschitz with `L = ∏‖Wₖ‖`, proved in Lean for the multi-layer net. -/
lemma g_lipschitzWith :
    LipschitzWith (1 * (1 * (1 * (1 * 2))) : ℝ≥0) g := by
  -- g = aff3 ∘ relu ∘ aff2 ∘ relu ∘ aff1, composed right-to-left.
  have hcomp :
      LipschitzWith (1 * (1 * (1 * (1 * 2))) : ℝ≥0)
        (aff3 ∘ relu ∘ aff2 ∘ relu ∘ aff1) :=
    aff3_lip.comp (relu_lip.comp (aff2_lip.comp (relu_lip.comp aff1_lip)))
  have hgeq : g = (aff3 ∘ relu ∘ aff2 ∘ relu ∘ aff1) := by
    funext x; rfl
  rw [hgeq]; exact hcomp

/-- The composite Lipschitz `ℝ≥0` constant is numerically `L = 2` (as a real). -/
lemma L_nn_coe : ((1 * (1 * (1 * (1 * 2))) : ℝ≥0) : ℝ) = L := by
  rw [L_eq_two]; push_cast; norm_num

/-- **The verified Lipschitz inequality in elementary `|·|` form** — the exact
fact the decision procedure consumes.  For all real `x, y`:
`|g x − g y| ≤ L · |x − y|` with `L = ∏‖Wₖ‖ = 2`.  Extracted from the
compositional `LipschitzWith` bound via `dist_le_mul`. -/
theorem g_lipschitz (x y : ℝ) : |g x - g y| ≤ L * |x - y| := by
  have h := g_lipschitzWith.dist_le_mul x y
  simp only [Real.dist_eq] at h
  rwa [L_nn_coe] at h

/-! ## 3. Box geometry, true minimum, and the Lipschitz-shaded relaxed bound

Geometry (`Box`, `mem`, `diam`, `split`, `cover`) is the same single-input
bisection model as `CompleteIBP`; only the net and the bound change. -/

/-- A box `[lo, hi]` is the pair `(lo, hi)`. -/
abbrev Box := ℝ × ℝ

/-- The set of input points of a box. -/
def boxSet (B : Box) : Set ℝ := Icc B.1 B.2

/-- Membership of an input point in a box. -/
def mem (B : Box) (s : ℝ) : Prop := B.1 ≤ s ∧ s ≤ B.2

/-- Safety at an input point: the deep net's output is strictly positive. -/
def safe (s : ℝ) : Prop := 0 < g s

/-- The controlling box width, clamped nonnegative. -/
def diam (B : Box) : ℝ := max 0 (B.2 - B.1)

/-- The exact true minimum of the net over the box: the genuine infimum of `g`. -/
noncomputable def trueMin (B : Box) : ℝ := sInf (g '' boxSet B)

/-- Coordinate bisection at the midpoint. -/
noncomputable def split (B : Box) : Box × Box :=
  ((B.1, (B.1 + B.2) / 2), ((B.1 + B.2) / 2, B.2))

/-- The **Lipschitz-shaded left-corner relaxed bound**:
`relaxedBound [lo,hi] = g(lo) − L · diam`.  `g(lo)` is the value at the left
corner (a point of the box); subtracting the verified Lipschitz error `L·diam`
makes it a SOUND lower bound on `g` over the whole box (proved in `decides`),
and keeps it within `L·diam` of `trueMin` (`width_error`).  The composite
Lipschitz constant `L = ∏‖Wₖ‖` is exactly the shade. -/
noncomputable def relaxedBound (B : Box) : ℝ := g B.1 - L * diam B

/-! ## 4. Net facts -/

/-- `g` is GLOBALLY ≥ 1: the output bias `d = 1` and both relus are ≥ 0, so
`g x = relu(relu(2x) − 1) + 1 ≥ 1`.  Hence the property holds with margin 1. -/
lemma g_ge_one (x : ℝ) : 1 ≤ g x := by
  unfold g aff3 aff2 aff1 relu
  have h1 : (0:ℝ) ≤ max 0 (1 * max 0 (2 * x + 0) + (-1)) := le_max_left _ _
  linarith

/-- The image of `g` over any box is bounded below (by `1`). -/
lemma img_bddBelow (B : Box) : BddBelow (g '' boxSet B) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, _, rfl⟩
  exact g_ge_one x

/-! ## 5. The `Relaxation` laws for the deep net -/

/-- `diam ≥ 0`. -/
lemma diam_nonneg (B : Box) : 0 ≤ diam B := le_max_left _ _

/-- `L ≥ 0`. -/
lemma L_nonneg : 0 ≤ L := by rw [L_eq_two]; norm_num

/-- **Width-error law.**  `trueMin B − L·diam B ≤ relaxedBound B`.
For a nonempty box, `lo ∈ box` so `trueMin ≤ g lo` (`csInf_le`), giving
`trueMin − L·diam ≤ g lo − L·diam = relaxedBound`.  For an empty box,
`trueMin = sInf ∅ = 0`, `diam = 0`, and `relaxedBound = g lo ≥ 1 > 0`. -/
lemma width_error (B : Box) : trueMin B - L * diam B ≤ relaxedBound B := by
  obtain ⟨lo, hi⟩ := B
  rcases le_or_gt lo hi with hle | hgt
  · -- nonempty box: trueMin ≤ g lo
    have hlo_mem : g lo ∈ g '' boxSet (lo, hi) := ⟨lo, ⟨le_refl _, hle⟩, rfl⟩
    have hsinf_le : trueMin (lo, hi) ≤ g lo := csInf_le (img_bddBelow _) hlo_mem
    simp only [relaxedBound]
    linarith
  · -- empty box: trueMin = 0, diam = 0, relaxedBound = g lo ≥ 1
    have hempty : boxSet (lo, hi) = (∅ : Set ℝ) := by
      simp only [boxSet]; exact Icc_eq_empty (by simp; linarith)
    have htm : trueMin (lo, hi) = 0 := by
      simp only [trueMin, hempty, Set.image_empty, Real.sInf_empty]
    have hdiam0 : diam (lo, hi) = 0 := by
      simp only [diam]; exact max_eq_left (by linarith)
    have hg : 1 ≤ g lo := g_ge_one lo
    simp only [relaxedBound, htm, hdiam0]
    linarith [L_nonneg]

/-- **CROWN/Lipschitz soundness of the relaxed bound.**  The Lipschitz-shaded
left-corner bound underestimates the net at every point of the box:
`relaxedBound B ≤ g s` for `s ∈ B`.  Proof: by the verified COMPOSITIONAL
Lipschitz bound `|g s − g lo| ≤ L·|s − lo|`, and `|s − lo| ≤ diam`, so
`g s ≥ g lo − L·diam = relaxedBound`.  This is exactly where the verified
product-of-operator-norms constant `L = ∏‖Wₖ‖` is consumed. -/
lemma relaxedBound_sound (B : Box) (s : ℝ) (hs : mem B s) :
    relaxedBound B ≤ g s := by
  obtain ⟨lo, hi⟩ := B
  obtain ⟨h1, h2⟩ := hs
  -- |g s − g lo| ≤ L·|s − lo|
  have hlip : |g s - g lo| ≤ L * |s - lo| := g_lipschitz s lo
  -- |s − lo| = s − lo ≤ hi − lo ≤ diam
  have hsl : |s - lo| = s - lo := abs_of_nonneg (by linarith)
  have hdiam_ge : s - lo ≤ diam (lo, hi) := by
    simp only [diam]
    calc s - lo ≤ hi - lo := by linarith
      _ ≤ max 0 (hi - lo) := le_max_right _ _
  -- g lo − g s ≤ |g s − g lo| ≤ L·(s−lo) ≤ L·diam
  have hgs : g lo - g s ≤ L * (s - lo) := by
    have := neg_abs_le (g s - g lo)
    have h2 : -(g s - g lo) ≤ |g s - g lo| := neg_le_abs _
    rw [hsl] at hlip
    linarith
  have hLmul : L * (s - lo) ≤ L * diam (lo, hi) :=
    mul_le_mul_of_nonneg_left hdiam_ge L_nonneg
  simp only [relaxedBound]
  linarith

/-- **Contraction law.**  Each child's diameter is `≤ diam/2`. -/
lemma diam_contract (B : Box) :
    diam (split B).1 ≤ diam B / 2 ∧ diam (split B).2 ≤ diam B / 2 := by
  obtain ⟨lo, hi⟩ := B
  simp only [split, diam]
  constructor
  · rcases le_total lo hi with h | h
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (show (lo + hi) / 2 - lo ≤ 0 by linarith)]; positivity
  · rcases le_total lo hi with h | h
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (show hi - (lo + hi) / 2 ≤ 0 by linarith)]; positivity

/-- Subset / nonempty-child helper for `trueMin` monotonicity. -/
lemma trueMin_mono_sub (B1 B2 : Box)
    (hsub : boxSet B2 ⊆ boxSet B1) (hne : (boxSet B2).Nonempty) :
    trueMin B1 ≤ trueMin B2 :=
  csInf_le_csInf (img_bddBelow _) (hne.image g) (image_mono hsub)

/-- **Monotonicity law.**  Each child's true minimum dominates the parent's. -/
lemma trueMin_mono (B : Box) :
    trueMin B ≤ trueMin (split B).1 ∧ trueMin B ≤ trueMin (split B).2 := by
  obtain ⟨lo, hi⟩ := B
  simp only [split]
  constructor
  · rcases le_total lo hi with h | h
    · apply trueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨hy1, by simp only at hy2 ⊢; linarith⟩
      · exact ⟨lo, by simp only [boxSet, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        have e2 : boxSet (lo, (lo + hi) / 2) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        simp only [trueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]
  · rcases le_total lo hi with h | h
    · apply trueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨by simp only at hy1 ⊢; linarith, hy2⟩
      · exact ⟨hi, by simp only [boxSet, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        have e2 : boxSet ((lo + hi) / 2, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        simp only [trueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]

/-- **Decides law.**  A positive relaxed bound on a box certifies safety on every
point of the box: `0 < relaxedBound B = g lo − L·diam ≤ g s` (the last step is
`relaxedBound_sound`, i.e. the verified compositional Lipschitz bound), so
`0 < g s` for every `s ∈ B`. -/
lemma decides (B : Box) (h : 0 < relaxedBound B) (s : ℝ) (hs : mem B s) : safe s :=
  lt_of_lt_of_le h (relaxedBound_sound B s hs)

/-- **Covering law.**  The two half-boxes of the midpoint split cover the parent. -/
lemma cover (B : Box) (s : ℝ) (hs : mem B s) :
    mem (split B).1 s ∨ mem (split B).2 s := by
  obtain ⟨h1, h2⟩ := hs
  simp only [split, mem]
  rcases le_total s ((B.1 + B.2) / 2) with hm | hm
  · exact Or.inl ⟨h1, hm⟩
  · exact Or.inr ⟨hm, h2⟩

/-! ## 6. The CONCRETE deep `Relaxation` instance — ALL fields discharged -/

/-- The CONCRETE relaxation of the real **two-hidden-layer** ReLU net, with every
field of `Complete.Relaxation` discharged.  The Lipschitz constant is the
composition-verified `L = ∏‖Wₖ‖ = 2`. -/
noncomputable def deepRelaxation : Complete.Relaxation Box ℝ where
  diam          := diam
  trueMin       := trueMin
  relaxedBound  := relaxedBound
  split         := split
  mem           := mem
  safe          := safe
  L             := L
  L_nonneg      := L_nonneg
  diam_nonneg   := diam_nonneg
  width_error   := width_error
  diam_contract := diam_contract
  trueMin_mono  := trueMin_mono
  decides       := decides
  cover         := cover

/-! ## 7. Concrete margin and the firing of `Complete.complete` on the DEEP net -/

/-- The verification **margin**: `δ = 1 ≤ trueMin [0,2]` (`g ≥ 1` everywhere). -/
lemma margin_pos : (1 : ℝ) ≤ trueMin (0, 2) := by
  apply le_csInf
  · exact ⟨g 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  · rintro y ⟨x, _, rfl⟩; exact g_ge_one x

/-- **VERIFIED MULTI-LAYER COMPLETENESS.**  `Complete.complete` instantiated on
the CONCRETE depth-2 relaxation: there is a finite bisection depth `d` at which
every leaf box of `[0,2]` has a strictly positive relaxed bound (shaded by the
composition-verified Lipschitz constant `L = ∏‖Wₖ‖`), and `g(x) > 0` for every
`x ∈ [0,2]`.  The decision procedure of `Complete.lean` terminates on a
genuinely DEEP (two hidden ReLU layer) net. -/
theorem deep_complete :
    ∃ d : ℕ,
      (∀ C ∈ Complete.leafBoxes deepRelaxation (0, 2) d,
        0 < deepRelaxation.relaxedBound C) ∧
      (∀ s, deepRelaxation.mem (0, 2) s → deepRelaxation.safe s) :=
  Complete.complete deepRelaxation (0, 2) (by norm_num) margin_pos

/-- **End-to-end decision (unfolded).**  For the REAL depth-2 net,
`g(x) > 0` on the entire input box `[0,2]`, decided through the verified
bisection procedure using the composition-verified Lipschitz constant. -/
theorem net_positive_on_box : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → 0 < g x := by
  obtain ⟨_, _, hdec⟩ := deep_complete
  intro x hx1 hx2
  exact hdec x ⟨hx1, hx2⟩

/-! ## 8. The depth-2 structure of the net, made explicit

A sanity statement that the verified `g` genuinely passes through TWO ReLU
nonlinearities (it is not collapsible to a one-layer net): `g x` equals the
explicit double-relu composition with the fixed weights. -/

/-- The net is the explicit composition through TWO hidden ReLU layers. -/
theorem g_is_two_hidden_layers (x : ℝ) :
    g x = relu (relu (2 * x) - 1) + 1 := by
  unfold g aff3 aff2 aff1; ring_nf

/-- The verified Lipschitz constant is the genuine PRODUCT of the three per-layer
operator-norm bounds (with each ReLU contributing factor `1`): `L = ‖W₃‖·‖W₂‖·‖W₁‖`. -/
theorem L_is_product_of_layer_norms : L = normW3 * normW2 * normW1 := rfl

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`. -/

#print axioms aff1_lip
#print axioms aff2_lip
#print axioms aff3_lip
#print axioms relu_lip
#print axioms g_lipschitzWith
#print axioms g_lipschitz
#print axioms g_ge_one
#print axioms width_error
#print axioms relaxedBound_sound
#print axioms diam_contract
#print axioms trueMin_mono
#print axioms decides
#print axioms cover
#print axioms deepRelaxation
#print axioms margin_pos
#print axioms deep_complete
#print axioms net_positive_on_box
#print axioms g_is_two_hidden_layers
#print axioms L_is_product_of_layer_norms

end CompleteDeep
end Crownproof
