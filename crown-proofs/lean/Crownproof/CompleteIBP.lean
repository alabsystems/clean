/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WAVE-2 PROGRAM 3 — INSTANTIATE the abstract completeness theorem on a CONCRETE,
REAL interval-bound-propagation (IBP) relaxation of an actual ReLU network.

────────────────────────────────────────────────────────────────────────────
WHAT iter-1 LEFT ABSTRACT, AND WHAT THIS FILE MAKES CONCRETE
────────────────────────────────────────────────────────────────────────────
`Complete.lean` proved the completeness CORE — "positive margin ⟹ finite
bisection decides the box" — over an ABSTRACT `Relaxation` structure whose three
analytic laws (`width_error`, `diam_contract`, `trueMin_mono`) plus `decides`
and `cover` were HYPOTHESES, and fired it only on a TOY affine witness
(`f = x + 10`, `L = 1`).  This file discharges EVERY field of that structure for
a CONCRETE, real relaxation: IBP on a genuine 1→2→1 ReLU network with exact
rational weights and a VERIFIED Lipschitz constant.  `Complete.complete` then
fires for THIS net.

────────────────────────────────────────────────────────────────────────────
THE NETWORK (concrete, exact-rational, defined inside Lean)
────────────────────────────────────────────────────────────────────────────
A 1-input → 2-hidden-ReLU → 1-output net:

      f(x) = v₁ · relu(w₁·x + c₁) + v₂ · relu(w₂·x + c₂) + d
           = 1 · relu(x)          + (−1) · relu(x − 1)      + 1
           = relu x − relu (x − 1) + 1.

  layer 1 (affine):  z₁ = x,  z₂ = x − 1            (W₁ = [1;1], b₁ = [0;−1])
  layer 1 (ReLU):    h₁ = relu z₁,  h₂ = relu z₂
  layer 2 (affine):  f  = h₁ − h₂ + 1               (W₂ = [1, −1], b₂ = 1)

Input box: x ∈ [0, 2].  Property to verify: f(x) > 0 on the box (`safe`).

VERIFIED Lipschitz constant.  Each ReLU is 1-Lipschitz; pre-activations are
affine with input-coefficients w₁ = w₂ = 1; the output combination has weights
v₁ = 1, v₂ = −1.  The operator-norm / sum-of-products bound is
      L = |v₁·w₁| + |v₂·w₂| = |1| + |−1| = 2,
and we PROVE the genuine analytic consequence used by `width_error` (the IBP
output bound is within `L·diam` of the true minimum) for THIS net.

────────────────────────────────────────────────────────────────────────────
WHY THIS IS A REAL TEST OF COMPLETENESS (IBP is genuinely loose here)
────────────────────────────────────────────────────────────────────────────
The exact minimum of `f` over `[0,2]` is `1` (`f ≡ 1` at `x = 0`, rising to `2`;
in fact `f` ranges over `[1,2]`), so the property holds with strict margin
`δ = 1 > 0`.  But IBP on the WHOLE box `[0,2]` returns only

      relaxedBound [0,2] = relu 0 − relu (2−1) + 1 = 0 − 1 + 1 = 0,

which is NOT `> 0`: IBP alone CANNOT decide the property — the relu over `[0,2]`
is unstable and IBP loses the correlation between the two hidden units.  A
SINGLE bisection fixes it: on `[0,1]` and `[1,2]` IBP returns `1 > 0` each
(`relaxedBound_left`, `relaxedBound_right` below).  This is exactly the scenario
completeness is about — a positive margin that input-IBP only certifies after
finite bisection — so firing `Complete.complete` here is meaningful, not vacuous.

────────────────────────────────────────────────────────────────────────────
WHAT IS CONCRETE vs WHAT REMAINS ABSTRACT (ruthless honesty)
────────────────────────────────────────────────────────────────────────────
CONCRETE (proved here, sorry-free):
  • the network `f` is defined inside Lean as an explicit relu composition;
  • `trueMin B` is the GENUINE exact minimum `sInf (f '' [lo,hi])` of the net's
    margin over the box — not an abstract placeholder;
  • `relaxedBound B` is the GENUINE IBP output lower bound for THIS net on the
    interval (forward interval propagation through the two relus, exact);
  • `L = 2` is the VERIFIED sum-of-products Lipschitz bound, and `width_error`
    is proved as a real analytic fact (IBP-soundness + relu 1-Lipschitzness);
  • ALL `Relaxation` fields are discharged; `Complete.complete` fires and the
    decisive depth is exhibited CONCRETELY (`decisive_depth_one`: depth 1).

SCOPE (stated honestly):
  • the net is a 1-hidden-layer (width-2) ReLU net over a 1-D input box, done
    RIGOROUSLY end-to-end.  The general multi-layer / multi-input IBP-Lipschitz
    `width_error` (the product-of-operator-norms argument across many layers,
    with per-coordinate interval propagation) is NOT formalised here; this file
    establishes the pattern on a real, non-trivial (IBP-loose) instance.  The
    abstract `Complete` core already covers any number of layers/inputs once a
    relaxation supplies the five laws; here we supply them for a concrete net.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete

namespace Crownproof
namespace CompleteIBP

open Set

/-! ## 1. The concrete network and its interval (IBP) bound

`relu` over ℝ as `max 0`; the net `f` is the explicit composition above. -/

/-- ReLU over the reals. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- The concrete 1→2→1 ReLU network:
`f x = relu x − relu (x − 1) + 1` (weights `v₁=1, v₂=−1, w₁=w₂=1, c₁=0, c₂=−1, d=1`). -/
def f (x : ℝ) : ℝ := relu x - relu (x - 1) + 1

/-- A box `[lo, hi]` is the pair `(lo, hi)`. -/
abbrev Box := ℝ × ℝ

/-- The set of input points of a box. -/
def boxSet (B : Box) : Set ℝ := Icc B.1 B.2

/-- Membership of an input point in a box. -/
def mem (B : Box) (s : ℝ) : Prop := B.1 ≤ s ∧ s ≤ B.2

/-- Safety at an input point: the net's margin is strictly positive. -/
def safe (s : ℝ) : Prop := 0 < f s

/-- The **controlling box width** (here the only input coordinate's length),
clamped to be nonnegative so it is total over all pairs. -/
def diam (B : Box) : ℝ := max 0 (B.2 - B.1)

/-- The verified **Lipschitz constant** `L = |v₁·w₁| + |v₂·w₂| = 2`. -/
def L : ℝ := 2

/-- The exact **true minimum** of the net's margin over the box: the genuine
infimum of `f` over `[lo, hi]`. -/
noncomputable def trueMin (B : Box) : ℝ := sInf (f '' boxSet B)

/-- The **IBP output lower bound** on the box.  Forward interval propagation:
`z₁ = x ∈ [lo, hi]`, `z₂ = x−1 ∈ [lo−1, hi−1]`; relu is monotone so
`relu z₁ ∈ [relu lo, relu hi]`, `relu z₂ ∈ [relu(lo−1), relu(hi−1)]`; the output
`relu z₁ − relu z₂ + 1` is minimised (lower-bounded) by taking the low end of
the `+`-term and the high end of the `−`-term:
`relaxedBound = relu lo − relu (hi − 1) + 1`. -/
def relaxedBound (B : Box) : ℝ := relu B.1 - relu (B.2 - 1) + 1

/-- Coordinate bisection at the midpoint: `[lo,hi] ↦ ([lo,m], [m,hi])`, `m=(lo+hi)/2`. -/
noncomputable def split (B : Box) : Box × Box :=
  ((B.1, (B.1 + B.2) / 2), ((B.1 + B.2) / 2, B.2))

/-! ## 2. Net facts:  bounds, IBP soundness, relu monotone-Lipschitz -/

/-- `f` is GLOBALLY bounded in `[1, 2]`: `relu x − relu (x−1) ∈ [0,1]`. -/
lemma f_bounds (x : ℝ) : 1 ≤ f x ∧ f x ≤ 2 := by
  unfold f relu
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 (x - 1) with hy | hy <;>
    simp only [max_eq_left, max_eq_right, hx, hy] <;> constructor <;> linarith

/-- The image of `f` over any box is bounded below (by `1`). -/
lemma img_bddBelow (B : Box) : BddBelow (f '' boxSet B) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, _, rfl⟩
  exact (f_bounds x).1

/-- **IBP soundness.** The IBP lower bound underestimates the net on every point
of the box: `relaxedBound B ≤ f s` for `s ∈ B`.  This is forward interval
propagation done soundly: `relu` is monotone, so `relu lo ≤ relu s` and
`relu (s−1) ≤ relu (hi−1)`. -/
lemma ibp_sound (B : Box) (s : ℝ) (hs : mem B s) : relaxedBound B ≤ f s := by
  obtain ⟨h1, h2⟩ := hs
  unfold relaxedBound f relu
  have ha : max 0 B.1 ≤ max 0 s := by
    rcases le_total 0 B.1 with hp | hp <;> rcases le_total 0 s with hq | hq <;>
      simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith
  have hb : max 0 (s - 1) ≤ max 0 (B.2 - 1) := by
    rcases le_total 0 (s - 1) with hp | hp <;> rcases le_total 0 (B.2 - 1) with hq | hq <;>
      simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith
  linarith

/-! ## 3. The five `Relaxation` laws for the concrete net -/

/-- `diam ≥ 0` for every pair (clamped definition). -/
lemma diam_nonneg (B : Box) : 0 ≤ diam B := le_max_left _ _

/-- **Width-error law (the core analytic fact).**
`trueMin B − L·diam B ≤ relaxedBound B` for THIS net, with `L = 2`.

Proof. For a nonempty box `[lo,hi]` (`lo ≤ hi`): `lo ∈ box`, so
`trueMin ≤ f lo` (`csInf_le`).  The IBP gap at the left endpoint is
`f lo − relaxedBound = relu(hi−1) − relu(lo−1)`, which is `≤ (hi−1)−(lo−1) = hi−lo`
by relu's 1-Lipschitzness (with `lo−1 ≤ hi−1`).  Hence
`trueMin ≤ f lo = relaxedBound + (relu(hi−1)−relu(lo−1)) ≤ relaxedBound + diam`,
so `trueMin − 2·diam ≤ trueMin − diam ≤ relaxedBound`.  For an empty box the
infimum is `0`, `diam = 0`, and `relaxedBound ≥ 1` (relu monotone, `lo > hi−1`). -/
lemma width_error (B : Box) : trueMin B - L * diam B ≤ relaxedBound B := by
  obtain ⟨lo, hi⟩ := B
  rcases le_or_gt lo hi with hle | hgt
  · -- nonempty box
    have hdiam : diam (lo, hi) = hi - lo := by
      simp only [diam]; exact max_eq_right (by linarith)
    have hlo_mem : f lo ∈ f '' boxSet (lo, hi) :=
      ⟨lo, ⟨le_refl _, hle⟩, rfl⟩
    have hsinf_le : trueMin (lo, hi) ≤ f lo := csInf_le (img_bddBelow _) hlo_mem
    -- relu(hi−1) − relu(lo−1) ≤ (hi−1) − (lo−1)
    have hmono : max 0 (hi - 1) - max 0 (lo - 1) ≤ (hi - 1) - (lo - 1) := by
      rcases le_total 0 (lo - 1) with hp | hp <;> rcases le_total 0 (hi - 1) with hq | hq <;>
        simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith
    -- f lo = relaxedBound + (relu(hi−1) − relu(lo−1))
    have hfeq : f lo = relaxedBound (lo, hi) + (max 0 (hi - 1) - max 0 (lo - 1)) := by
      unfold f relaxedBound relu; ring
    rw [hfeq] at hsinf_le
    simp only [L, hdiam]
    linarith
  · -- empty box: trueMin = sInf ∅ = 0
    have hempty : boxSet (lo, hi) = (∅ : Set ℝ) := by
      simp only [boxSet]; exact Icc_eq_empty (by simp; linarith)
    have htm : trueMin (lo, hi) = 0 := by
      simp only [trueMin, hempty, Set.image_empty, Real.sInf_empty]
    have hdiam0 : diam (lo, hi) = 0 := by
      simp only [diam]; exact max_eq_left (by linarith)
    -- relaxedBound ≥ 1:  relu(hi−1) ≤ relu lo since lo > hi−1
    have hrelu : max 0 (hi - 1) ≤ max 0 lo := by
      rcases le_total 0 (hi - 1) with hp | hp <;> rcases le_total 0 lo with hq | hq <;>
        simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith
    simp only [L, htm, hdiam0, relaxedBound, relu]
    linarith

/-- **Contraction law.** Each child's (clamped) diameter is `≤ diam/2`. -/
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

/-- A subset, nonempty-child helper for monotonicity of `trueMin`. -/
lemma trueMin_mono_sub (B1 B2 : Box)
    (hsub : boxSet B2 ⊆ boxSet B1) (hne : (boxSet B2).Nonempty) :
    trueMin B1 ≤ trueMin B2 :=
  csInf_le_csInf (img_bddBelow _) (hne.image f) (image_mono hsub)

/-- **Monotonicity law.** Each child's true minimum dominates the parent's:
the infimum over a sub-box is at least the infimum over the box. -/
lemma trueMin_mono (B : Box) :
    trueMin B ≤ trueMin (split B).1 ∧ trueMin B ≤ trueMin (split B).2 := by
  obtain ⟨lo, hi⟩ := B
  simp only [split]
  constructor
  · -- left child [lo, m]
    rcases le_total lo hi with h | h
    · apply trueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨hy1, by simp only at hy2 ⊢; linarith⟩
      · exact ⟨lo, by simp only [boxSet, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        have e2 : boxSet (lo, (lo + hi) / 2) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        simp only [trueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]
  · -- right child [m, hi]
    rcases le_total lo hi with h | h
    · apply trueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨by simp only at hy1 ⊢; linarith, hy2⟩
      · exact ⟨hi, by simp only [boxSet, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        have e2 : boxSet ((lo + hi) / 2, hi) = (∅ : Set ℝ) := Icc_eq_empty (by simp; linarith)
        simp only [trueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]

/-- **Decides law.** A positive IBP bound on a box certifies safety on every
point of the box (this is the soundness leaf certificate, here = IBP soundness). -/
lemma decides (B : Box) (h : 0 < relaxedBound B) (s : ℝ) (hs : mem B s) : safe s :=
  lt_of_lt_of_le h (ibp_sound B s hs)

/-- **Covering law.** The two half-boxes of the midpoint split cover the parent. -/
lemma cover (B : Box) (s : ℝ) (hs : mem B s) :
    mem (split B).1 s ∨ mem (split B).2 s := by
  obtain ⟨h1, h2⟩ := hs
  simp only [split, mem]
  rcases le_total s ((B.1 + B.2) / 2) with hm | hm
  · exact Or.inl ⟨h1, hm⟩
  · exact Or.inr ⟨hm, h2⟩

/-! ## 4. The concrete `Relaxation` instance — ALL fields discharged -/

/-- The CONCRETE IBP relaxation of the real 1→2→1 ReLU net, with every field of
`Complete.Relaxation` discharged by the lemmas above. -/
noncomputable def ibpRelaxation : Complete.Relaxation Box ℝ where
  diam          := diam
  trueMin       := trueMin
  relaxedBound  := relaxedBound
  split         := split
  mem           := mem
  safe          := safe
  L             := L
  L_nonneg      := by norm_num [L]
  diam_nonneg   := diam_nonneg
  width_error   := width_error
  diam_contract := diam_contract
  trueMin_mono  := trueMin_mono
  decides       := decides
  cover         := cover

/-! ## 5. Concrete margin and the IBP-looseness witness -/

/-- The verification **margin** is strict-positive: `δ = 1 ≤ trueMin [0,2]`.
(`f ≥ 1` everywhere, so its infimum over the box is `≥ 1`.) -/
lemma margin_pos : (1 : ℝ) ≤ trueMin (0, 2) := by
  apply le_csInf
  · exact ⟨f 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  · rintro y ⟨x, _, rfl⟩; exact (f_bounds x).1

/-- **IBP alone is genuinely loose on the root box.** On `[0,2]` the IBP bound is
exactly `0` — NOT `> 0` — so plain IBP cannot decide `f > 0`; bisection is
needed.  This makes the completeness firing below non-vacuous. -/
lemma relaxedBound_root_zero : relaxedBound ((0 : ℝ), 2) = 0 := by
  unfold relaxedBound relu; norm_num

/-- After ONE bisection both leaves close: IBP on `[0,1]` is `1 > 0`. -/
lemma relaxedBound_left : 0 < relaxedBound ((0 : ℝ), 1) := by
  unfold relaxedBound relu; norm_num

/-- … and IBP on `[1,2]` is `1 > 0`. -/
lemma relaxedBound_right : 0 < relaxedBound ((1 : ℝ), 2) := by
  unfold relaxedBound relu; norm_num

/-! ## 6. `Complete.complete` FIRES on the concrete net

The abstract completeness theorem, instantiated at `ibpRelaxation`, decides the
property `safe` (`f > 0`) on the whole input box `[0,2]` by finite bisection. -/

/-- **The instantiation.**  `Complete.complete` on the CONCRETE IBP relaxation:
there is a finite bisection depth `d` at which every leaf box of `[0,2]` has a
strictly positive IBP bound, and `f(x) > 0` for every `x ∈ [0,2]`.  The decisive
depth is a concrete finite number (existence via the Archimedean bound; an
explicit witness `d = 1` is given in `decisive_depth_one`). -/
theorem ibp_complete :
    ∃ d : ℕ,
      (∀ C ∈ Complete.leafBoxes ibpRelaxation (0, 2) d,
        0 < ibpRelaxation.relaxedBound C) ∧
      (∀ s, ibpRelaxation.mem (0, 2) s → ibpRelaxation.safe s) :=
  Complete.complete ibpRelaxation (0, 2) (by norm_num) margin_pos

/-- **End-to-end decision (unfolded).**  For the REAL net, `f(x) > 0` on the
entire input box `[0,2]`, decided through the verified bisection procedure. -/
theorem net_positive_on_box : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → 0 < f x := by
  obtain ⟨_, _, hdec⟩ := ibp_complete
  intro x hx1 hx2
  exact hdec x ⟨hx1, hx2⟩

/-- **The decisive depth is concretely `1`.**  The two depth-1 leaf boxes of the
full bisection of `[0,2]` are exactly `[0,1]` and `[1,2]`, and IBP returns a
strictly positive bound on each — so one bisection suffices to close every leaf
(matching the genuine looseness of `relaxedBound_root_zero`). -/
theorem decisive_depth_one :
    ∀ C ∈ Complete.leafBoxes ibpRelaxation (0, 2) 1,
      0 < ibpRelaxation.relaxedBound C := by
  intro C hC
  -- leafBoxes _ (0,2) 1 = leafBoxes left 0 ++ leafBoxes right 0 = [left] ++ [right]
  simp only [Complete.leafBoxes, ibpRelaxation, split, List.mem_append,
    List.mem_singleton] at hC
  -- left child of (0,2) is (0, 1); right child is (1, 2)
  rcases hC with hC | hC <;> subst hC
  · -- C = ((0,2).1, ((0,2).1+(0,2).2)/2) = (0, 1)
    show 0 < relaxedBound (0, (0 + 2) / 2)
    unfold relaxedBound relu; norm_num
  · -- C = (((0,2).1+(0,2).2)/2, (0,2).2) = (1, 2)
    show 0 < relaxedBound ((0 + 2) / 2, 2)
    unfold relaxedBound relu; norm_num

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`. -/

#print axioms f_bounds
#print axioms ibp_sound
#print axioms width_error
#print axioms diam_contract
#print axioms trueMin_mono
#print axioms decides
#print axioms cover
#print axioms ibpRelaxation
#print axioms margin_pos
#print axioms relaxedBound_root_zero
#print axioms ibp_complete
#print axioms net_positive_on_box
#print axioms decisive_depth_one

end CompleteIBP
end Crownproof
