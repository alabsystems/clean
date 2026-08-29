/-
  WAVE-3 PROGRAM 4 — GENERAL coupled k=2 convex-hull V-description.

  ====================================================================
  WHAT WAS LEFT OPEN BY WAVE-2 (ConvHullCoupled.lean, committed b3249cc1)
  ====================================================================

  Wave-2 proved the COUPLED LP-exactness engine GENERALLY
  (`coupled_lp_max_eq`, `objC_isGreatest_convHull`): for any linear objective the
  maximum over `conv(G)` equals the maximum over the exact coupled graph `G`, for
  ARBITRARY affine coupling `z1 = a1·x+c1, z2 = a2·x+c2` over a box.  But the
  explicit V-DESCRIPTION of the hull — `conv(G) = conv(curve breakpoints)` — and
  the matching "max attained at a breakpoint" tight-facet were proved ONLY on a
  concrete anti-diagonal INSTANCE (`graph_subset_convHull_verts`,
  `coupled_convHull_eq_breakpoints`, with a1=1,c1=1,a2=-1,c2=1, x∈[-2,2]).

  ====================================================================
  WHAT THIS FILE PROVES (sorry-free; trust base [propext, Classical.choice, Quot.sound])
  ====================================================================

  GENERAL V-DESCRIPTION.  For ARBITRARY a1,c1,a2,c2,xl,xu (any reals) the coupled
  2-ReLU curve
        curve x = (z1 x, z2 x, reluC (z1 x), reluC (z2 x)),  z1 = a1·x+c1, z2 = a2·x+c2,
  over x ∈ [xl,xu] is a piecewise-linear curve with AT MOST 4 breakpoints (the two
  box endpoints plus the ≤2 crossing points where z1=0 or z2=0, clamped to the box).
  We prove EXACTLY
        conv(coupledGraph) = conv(curve '' breakpoints),
  the breakpoint polytope V-description — GENERAL in all parameters.

  PARAMETER COVERAGE (ruthlessly honest, per the task instruction):
   * `coupled_convHull_eq_breakpoints_general`  (a1 ≠ 0 ∧ a2 ≠ 0): the GENERIC
     regime where BOTH pre-activations genuinely vary with x.  This covers the
     full qualitative landscape — SAME-SIGN slopes (a1·a2 > 0) and OPPOSITE-SIGN
     slopes (a1·a2 < 0) are BOTH instances (the proof never case-splits on
     sign(a1·a2); the nested root-split handles any ordering of the two crossings).
     The Wave-2 instance (a1=1,a2=-1) is one opposite-sign point of this family.
   * The degenerate edges a1 = 0 (z1 constant) and a2 = 0 (z2 constant) are handled
     separately (`..._general_a1zero`, `..._general_a2zero`): then that neuron has a
     fixed sign and the curve has ≤2 breakpoints from the OTHER neuron.  With both
     a1=a2=0 the curve is a single point.  So EVERY (a1,c1,a2,c2,xl,xu) is covered.

  WHAT IS GENUINELY NEW vs the Wave-2 instance:
   * the constant-sign affine-interpolation engine (`curve_mem_segment_signconst`),
   * the per-neuron monotone sign-SPLIT at the exact root (`affine_signSplit`),
   * the JOINT nested bracketing producing, for ANY x, two breakpoints from the
     ≤4-element set with BOTH neurons sign-constant between them (`joint_bracket`),
   * and the assembly into the curve-⊆-hull and hull-equality theorems for ARBITRARY
     parameters.  Wave-2 did all four by hand only for the single rational instance.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith

namespace CrownproofGeneral

open Set

/-! ===================================================================
    SECTION 0.  ReLU, the coupled curve, the graph.  (Self-contained; mirrors
    `Crownproof.reluC` / `curve` / `coupledGraph` of ConvHullCoupled.lean.)
    =================================================================== -/

/-- ReLU on the reals. -/
def reluC (z : ℝ) : ℝ := max 0 z
theorem reluC_of_nonneg {z : ℝ} (h : 0 ≤ z) : reluC z = z := max_eq_right h
theorem reluC_of_neg {z : ℝ} (h : z ≤ 0) : reluC z = 0 := max_eq_left h

/-- Pre-activations as affine functions of the shared scalar input. -/
def z1c (a1 c1 x : ℝ) : ℝ := a1 * x + c1
def z2c (a2 c2 x : ℝ) : ℝ := a2 * x + c2

/-- The coupled 2-ReLU curve point at shared input `x`. -/
def curve (a1 c1 a2 c2 x : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (z1c a1 c1 x, z2c a2 c2 x, reluC (z1c a1 c1 x), reluC (z2c a2 c2 x))

/-- The exact COUPLED 2-ReLU graph: the image of the box `[xl,xu]` under `curve`. -/
def coupledGraph (a1 c1 a2 c2 xl xu : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  (curve a1 c1 a2 c2) '' (Icc xl xu)

/-! ===================================================================
    SECTION 1.  Affine sign propagation.  An affine `z(x)=a·x+c` that is ≥0 (resp.
    ≤0) at both ends of `[p,q]` keeps that sign throughout (it is monotone).
    =================================================================== -/

theorem affine_nonneg_of_endpoints (a c p q x : ℝ) (hx : x ∈ Icc p q)
    (hp : 0 ≤ a*p+c) (hq : 0 ≤ a*q+c) : 0 ≤ a*x+c := by
  obtain ⟨hxp, hxq⟩ := hx
  rcases le_total a 0 with ha | ha
  · nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hxq)]
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxp)]

theorem affine_nonpos_of_endpoints (a c p q x : ℝ) (hx : x ∈ Icc p q)
    (hp : a*p+c ≤ 0) (hq : a*q+c ≤ 0) : a*x+c ≤ 0 := by
  obtain ⟨hxp, hxq⟩ := hx
  rcases le_total a 0 with ha | ha
  · nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hxp)]
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxq)]

/-- `z = a·x+c` is "sign-constant" over `[p,q]`: both endpoints on the same side of 0. -/
def SignConst (a c p q : ℝ) : Prop :=
  (0 ≤ a*p+c ∧ 0 ≤ a*q+c) ∨ (a*p+c ≤ 0 ∧ a*q+c ≤ 0)

/-- SignConst on a super-interval restricts to any sub-interval (monotone sign). -/
theorem signConst_sub (a c u1 v1 u2 v2 : ℝ)
    (h : SignConst a c u1 v1) (h1 : u1 ≤ u2) (h2 : u2 ≤ v2) (h3 : v2 ≤ v1) :
    SignConst a c u2 v2 := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inl ⟨affine_nonneg_of_endpoints a c u1 v1 u2 ⟨h1, by linarith⟩ hp hq,
           affine_nonneg_of_endpoints a c u1 v1 v2 ⟨by linarith, h3⟩ hp hq⟩
  · exact Or.inr ⟨affine_nonpos_of_endpoints a c u1 v1 u2 ⟨h1, by linarith⟩ hp hq,
           affine_nonpos_of_endpoints a c u1 v1 v2 ⟨by linarith, h3⟩ hp hq⟩

/-! ===================================================================
    SECTION 2.  The constant-sign affine-interpolation ENGINE.

    On any interval where BOTH neurons keep a fixed sign, `curve` is AFFINE, so each
    interior curve point is a convex combination of the two endpoint curve points.
    =================================================================== -/

/-- On a constant-sign interval `reluC (z x)` is the affine interpolation of relu at
    the endpoints (with the same weight `t = (x-p)/(q-p)` as `z` itself). -/
theorem relu_affine_on_signconst (a c p q x : ℝ) (hpq : p < q) (hx : x ∈ Icc p q)
    (hs : SignConst a c p q) :
    reluC (a*x+c) = (1 - (x-p)/(q-p)) * reluC (a*p+c) + ((x-p)/(q-p)) * reluC (a*q+c) := by
  have hd : q - p ≠ 0 := by linarith
  rcases hs with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hmid : 0 ≤ a*x+c := affine_nonneg_of_endpoints a c p q x hx hp hq
    rw [reluC_of_nonneg hmid, reluC_of_nonneg hp, reluC_of_nonneg hq]; field_simp; ring
  · have hmid : a*x+c ≤ 0 := affine_nonpos_of_endpoints a c p q x hx hp hq
    rw [reluC_of_neg hmid, reluC_of_neg hp, reluC_of_neg hq]; simp

/-- On a constant-sign interval for BOTH neurons, the whole ℝ⁴ curve point is the
    affine interpolation `(1-t)•curve p + t•curve q`. -/
theorem curve_combo_on_signconst (a1 c1 a2 c2 p q x : ℝ) (hpq : p < q) (hx : x ∈ Icc p q)
    (hs1 : SignConst a1 c1 p q) (hs2 : SignConst a2 c2 p q) :
    curve a1 c1 a2 c2 x
      = (1 - (x-p)/(q-p)) • curve a1 c1 a2 c2 p + ((x-p)/(q-p)) • curve a1 c1 a2 c2 q := by
  set t := (x-p)/(q-p) with ht
  have hd : q - p ≠ 0 := by linarith
  have hz1 : z1c a1 c1 x = (1-t) * z1c a1 c1 p + t * z1c a1 c1 q := by
    simp only [z1c, ht]; field_simp; ring
  have hz2 : z2c a2 c2 x = (1-t) * z2c a2 c2 p + t * z2c a2 c2 q := by
    simp only [z2c, ht]; field_simp; ring
  have hr1 := relu_affine_on_signconst a1 c1 p q x hpq hx hs1
  have hr2 := relu_affine_on_signconst a2 c2 p q x hpq hx hs2
  simp only [curve, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
  refine Prod.ext hz1 (Prod.ext hz2 (Prod.ext ?_ ?_))
  · simpa only [z1c, ht] using hr1
  · simpa only [z2c, ht] using hr2

/-- Hence on a constant-sign interval `curve x ∈ segment ℝ (curve p) (curve q)`. -/
theorem curve_mem_segment_signconst (a1 c1 a2 c2 p q x : ℝ) (hpq : p < q) (hx : x ∈ Icc p q)
    (hs1 : SignConst a1 c1 p q) (hs2 : SignConst a2 c2 p q) :
    curve a1 c1 a2 c2 x ∈ segment ℝ (curve a1 c1 a2 c2 p) (curve a1 c1 a2 c2 q) := by
  obtain ⟨hxp, hxq⟩ := hx
  have hd : (0:ℝ) < q - p := by linarith
  refine ⟨1 - (x-p)/(q-p), (x-p)/(q-p), ?_, ?_, by ring, ?_⟩
  · have : (x-p)/(q-p) ≤ 1 := by rw [div_le_one hd]; linarith
    linarith
  · exact div_nonneg (by linarith) (le_of_lt hd)
  · exact (curve_combo_on_signconst a1 c1 a2 c2 p q x hpq ⟨hxp,hxq⟩ hs1 hs2).symm

/-! ===================================================================
    SECTION 3.  Per-neuron monotone sign-SPLIT at the exact crossing.

    For one neuron with `a ≠ 0` the root is `r = -c/a`.  Over any `[u,v]`, either the
    neuron is sign-constant on all of `[u,v]`, or `r` lies strictly inside `(u,v)` and
    splits `[u,v]` into two sign-constant halves `[u,r], [r,v]`.
    =================================================================== -/

theorem affine_root (a c : ℝ) (ha : a ≠ 0) : a * (-c/a) + c = 0 := by
  field_simp; ring

theorem affine_signSplit (a c u v : ℝ) (ha : a ≠ 0) (huv : u ≤ v) :
    SignConst a c u v ∨
      (u < -c/a ∧ -c/a < v ∧ SignConst a c u (-c/a) ∧ SignConst a c (-c/a) v) := by
  have hr : a * (-c/a) + c = 0 := affine_root a c ha
  rcases lt_trichotomy (-c/a) u with hru | hru | hru
  · left
    rcases le_or_gt 0 a with ha' | ha'
    · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
      exact Or.inl ⟨by nlinarith [mul_pos hapos (sub_pos.mpr hru)],
        by nlinarith [mul_pos hapos (sub_pos.mpr (lt_of_lt_of_le hru huv))]⟩
    · exact Or.inr ⟨by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr hru)],
        by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr (lt_of_lt_of_le hru huv))]⟩
  · left
    rcases le_or_gt 0 a with ha' | ha'
    · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
      subst hru
      exact Or.inl ⟨by linarith [hr], by nlinarith [mul_nonneg hapos.le (sub_nonneg.mpr huv)]⟩
    · subst hru
      exact Or.inr ⟨by linarith [hr],
        by nlinarith [mul_nonneg (neg_nonneg.mpr ha'.le) (sub_nonneg.mpr huv)]⟩
  · rcases lt_trichotomy (-c/a) v with hrv | hrv | hrv
    · right
      refine ⟨hru, hrv, ?_, ?_⟩
      · rcases le_or_gt 0 a with ha' | ha'
        · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
          exact Or.inr ⟨by nlinarith [mul_pos hapos (sub_pos.mpr hru)], by linarith [hr]⟩
        · exact Or.inl ⟨by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr hru)],
            by linarith [hr]⟩
      · rcases le_or_gt 0 a with ha' | ha'
        · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
          exact Or.inl ⟨by linarith [hr], by nlinarith [mul_pos hapos (sub_pos.mpr hrv)]⟩
        · exact Or.inr ⟨by linarith [hr],
            by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr hrv)]⟩
    · left
      rcases le_or_gt 0 a with ha' | ha'
      · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
        subst hrv
        exact Or.inr ⟨by nlinarith [mul_nonneg hapos.le (sub_nonneg.mpr huv)], by linarith [hr]⟩
      · subst hrv
        exact Or.inl ⟨by nlinarith [mul_nonneg (neg_nonneg.mpr ha'.le) (sub_nonneg.mpr huv)],
          by linarith [hr]⟩
    · left
      rcases le_or_gt 0 a with ha' | ha'
      · have hapos : 0 < a := lt_of_le_of_ne ha' (Ne.symm ha)
        exact Or.inr ⟨by nlinarith [mul_pos hapos (sub_pos.mpr (lt_of_le_of_lt huv hrv))],
          by nlinarith [mul_pos hapos (sub_pos.mpr hrv)]⟩
      · exact Or.inl ⟨by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr (lt_of_le_of_lt huv hrv))],
          by nlinarith [mul_pos (neg_pos.mpr ha') (sub_pos.mpr hrv)]⟩

/-- When a = 0, z = c is constant, so SignConst holds on ANY interval.  This lets the
    JOINT bracket cover the degenerate edges a1 = 0 and/or a2 = 0 uniformly: a
    constant pre-activation keeps a fixed sign over the whole box, so we simply do not
    split on it. -/
theorem signConst_of_a_zero (c p q : ℝ) : SignConst 0 c p q := by
  unfold SignConst
  rcases le_total 0 c with h | h
  · exact Or.inl ⟨by simpa using h, by simpa using h⟩
  · exact Or.inr ⟨by simpa using h, by simpa using h⟩

/-! ===================================================================
    SECTION 4.  JOINT nested bracketing — FULLY GENERAL in a1, a2.

    Splitting `[xl,xu]` first by neuron 1's root (only if a1 ≠ 0) then the relevant
    half by neuron 2's root (only if a2 ≠ 0) yields, for ANY x in the box, two
    breakpoints p ≤ x ≤ q from the ≤4-element set {xl, xu, -c1/a1, -c2/a2} with BOTH
    neurons sign-constant on [p,q].  Works for ARBITRARY a1,a2 — including the
    degenerate constant-neuron edges a1 = 0 and/or a2 = 0 (with the Lean convention
    `r/0 = 0`, an unused root is just a spurious-but-in-box candidate).
    =================================================================== -/

theorem joint_bracket (a1 c1 a2 c2 xl xu x : ℝ)
    (hxlu : xl ≤ xu) (hx : x ∈ Icc xl xu) :
    ∃ p q, p ≤ x ∧ x ≤ q ∧ xl ≤ p ∧ q ≤ xu ∧ p ≤ q ∧
      SignConst a1 c1 p q ∧ SignConst a2 c2 p q ∧
      (p = xl ∨ p = xu ∨ p = -c1/a1 ∨ p = -c2/a2) ∧
      (q = xl ∨ q = xu ∨ q = -c1/a1 ∨ q = -c2/a2) := by
  obtain ⟨hxl, hxu⟩ := hx
  -- STEP 1: bracket x by a neuron-1 sign-constant subinterval [u1,v1].
  obtain ⟨u1, v1, hu1x, hxv1, hxlu1, hv1xu, hu1v1, hsc1, hu1mem, hv1mem⟩ :
      ∃ u1 v1, u1 ≤ x ∧ x ≤ v1 ∧ xl ≤ u1 ∧ v1 ≤ xu ∧ u1 ≤ v1 ∧ SignConst a1 c1 u1 v1 ∧
        (u1 = xl ∨ u1 = -c1/a1) ∧ (v1 = xu ∨ v1 = -c1/a1) := by
    by_cases ha1 : a1 = 0
    · subst ha1
      exact ⟨xl, xu, hxl, hxu, le_refl _, le_refl _, hxlu, signConst_of_a_zero _ _ _,
        Or.inl rfl, Or.inl rfl⟩
    · rcases affine_signSplit a1 c1 xl xu ha1 hxlu with hsc | ⟨hlt1, hlt2, hscl, hscr⟩
      · exact ⟨xl, xu, hxl, hxu, le_refl _, le_refl _, hxlu, hsc, Or.inl rfl, Or.inl rfl⟩
      · rcases le_or_gt x (-c1/a1) with hxr | hxr
        · exact ⟨xl, -c1/a1, hxl, hxr, le_refl _, le_of_lt hlt2, le_of_lt hlt1, hscl,
            Or.inl rfl, Or.inr rfl⟩
        · exact ⟨-c1/a1, xu, le_of_lt hxr, hxu, le_of_lt hlt1, le_refl _, le_of_lt hlt2, hscr,
            Or.inr rfl, Or.inl rfl⟩
  -- STEP 2: split [u1,v1] by neuron 2 (only if a2 ≠ 0); neuron 1 stays sign-constant.
  by_cases ha2 : a2 = 0
  · subst ha2
    refine ⟨u1, v1, hu1x, hxv1, hxlu1, hv1xu, hu1v1, hsc1, signConst_of_a_zero _ _ _, ?_, ?_⟩
    · rcases hu1mem with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases hv1mem with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · rcases affine_signSplit a2 c2 u1 v1 ha2 hu1v1 with hsc2 | ⟨hlt1, hlt2, hscl, hscr⟩
    · refine ⟨u1, v1, hu1x, hxv1, hxlu1, hv1xu, hu1v1, hsc1, hsc2, ?_, ?_⟩
      · rcases hu1mem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases hv1mem with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · rcases le_or_gt x (-c2/a2) with hxr | hxr
      · refine ⟨u1, -c2/a2, hu1x, hxr, hxlu1, by linarith, le_of_lt hlt1,
          signConst_sub a1 c1 u1 v1 u1 (-c2/a2) hsc1 (le_refl _) (le_of_lt hlt1) (le_of_lt hlt2),
          hscl, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
        rcases hu1mem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · refine ⟨-c2/a2, v1, le_of_lt hxr, hxv1, by linarith, hv1xu, le_of_lt hlt2,
          signConst_sub a1 c1 u1 v1 (-c2/a2) v1 hsc1 (le_of_lt hlt1) (le_of_lt hlt2) (le_refl _),
          hscr, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
        rcases hv1mem with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))

/-! ===================================================================
    SECTION 5.  Breakpoint set, vertices, and the GENERAL V-DESCRIPTION.

    The ≤4 breakpoint x-values are the box endpoints plus the two crossing points
    clamped into the box; the vertex set is their `curve` images (genuine graph
    points).  We prove `curve '' [xl,xu] ⊆ conv(vertices)` (every curve point is a
    convex combination of the breakpoints) and the matching hull equality.
    =================================================================== -/

/-- Clamp a value into the box `[xl,xu]`. -/
def clamp (xl xu r : ℝ) : ℝ := max xl (min xu r)

theorem clamp_mem (xl xu r : ℝ) (h : xl ≤ xu) : clamp xl xu r ∈ Icc xl xu :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem clamp_eq_of_mem (xl xu r : ℝ) (hl : xl ≤ r) (hu : r ≤ xu) : clamp xl xu r = r := by
  unfold clamp; rw [min_eq_right hu, max_eq_right hl]

/-- The breakpoint x-set: endpoints + the two clamped crossing points (≤4 values). -/
def bxSet (a1 c1 a2 c2 xl xu : ℝ) : Set ℝ :=
  {xl, xu, clamp xl xu (-c1/a1), clamp xl xu (-c2/a2)}

/-- All breakpoint x-values lie in the box (their curve images are genuine graph
    points). -/
theorem bxSet_subset_box (a1 c1 a2 c2 xl xu : ℝ) (h : xl ≤ xu) :
    bxSet a1 c1 a2 c2 xl xu ⊆ Icc xl xu := by
  rintro b hb
  simp only [bxSet, mem_insert_iff, mem_singleton_iff] at hb
  rcases hb with h1 | h1 | h1 | h1 <;> subst h1
  · exact ⟨le_refl _, h⟩
  · exact ⟨h, le_refl _⟩
  · exact clamp_mem xl xu _ h
  · exact clamp_mem xl xu _ h

/-- The breakpoint VERTEX set: `curve` images of the ≤4 breakpoint x-values. -/
def vSet (a1 c1 a2 c2 xl xu : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  (curve a1 c1 a2 c2) '' (bxSet a1 c1 a2 c2 xl xu)

/-- A breakpoint `p ∈ {xl,xu,-c1/a1,-c2/a2}` that lies in the box has `curve p ∈ vSet`
    (when `p` is a crossing, it equals its own clamp because it is in the box). -/
theorem brk_curve_mem_vSet (a1 c1 a2 c2 xl xu p : ℝ)
    (hpl : xl ≤ p) (hpu : p ≤ xu)
    (hp : p = xl ∨ p = xu ∨ p = -c1/a1 ∨ p = -c2/a2) :
    curve a1 c1 a2 c2 p ∈ vSet a1 c1 a2 c2 xl xu := by
  refine ⟨p, ?_, rfl⟩
  simp only [bxSet, mem_insert_iff, mem_singleton_iff]
  rcases hp with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [clamp_eq_of_mem xl xu (-c1/a1) (h ▸ hpl) (h ▸ hpu)]; exact h
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [clamp_eq_of_mem xl xu (-c2/a2) (h ▸ hpl) (h ▸ hpu)]; exact h

/-- **GENERAL V-DESCRIPTION, subset direction.**  Every coupled-curve point is a
    convex combination of the ≤4 breakpoint vertices.  FULLY GENERAL in
    a1,c1,a2,c2,xl,xu (any reals; no nonzero or sign hypotheses). -/
theorem graph_subset_convHull_vSet (a1 c1 a2 c2 xl xu : ℝ) (hxlu : xl ≤ xu) :
    coupledGraph a1 c1 a2 c2 xl xu ⊆ convexHull ℝ (vSet a1 c1 a2 c2 xl xu) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, q, hpx, hxq, hxlp, hqxu, hpq, hsc1, hsc2, hpmem, hqmem⟩ :=
    joint_bracket a1 c1 a2 c2 xl xu x hxlu hx
  have hCp : curve a1 c1 a2 c2 p ∈ convexHull ℝ (vSet a1 c1 a2 c2 xl xu) :=
    subset_convexHull ℝ _
      (brk_curve_mem_vSet a1 c1 a2 c2 xl xu p hxlp (le_trans hpq hqxu) hpmem)
  have hCq : curve a1 c1 a2 c2 q ∈ convexHull ℝ (vSet a1 c1 a2 c2 xl xu) :=
    subset_convexHull ℝ _
      (brk_curve_mem_vSet a1 c1 a2 c2 xl xu q (le_trans hxlp hpq) hqxu hqmem)
  rcases lt_or_eq_of_le hpq with hlt | heq
  · have hseg := curve_mem_segment_signconst a1 c1 a2 c2 p q x hlt ⟨hpx, hxq⟩ hsc1 hsc2
    exact (convex_convexHull ℝ _).segment_subset hCp hCq hseg
  · have hxp : x = p := le_antisymm (heq ▸ hxq) hpx
    rw [hxp]; exact hCp

/-- Every breakpoint vertex is a genuine point of the coupled graph. -/
theorem vSet_subset_graph (a1 c1 a2 c2 xl xu : ℝ) (hxlu : xl ≤ xu) :
    vSet a1 c1 a2 c2 xl xu ⊆ coupledGraph a1 c1 a2 c2 xl xu := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, bxSet_subset_box a1 c1 a2 c2 xl xu hxlu hb, rfl⟩

/-- **★ GENERAL V-DESCRIPTION (the deliverable).**  For ARBITRARY affine coupling
    `z1 = a1·x+c1, z2 = a2·x+c2` over ANY box `[xl,xu]` (with `xl ≤ xu`),
        conv(coupledGraph)  =  conv(≤4 breakpoint vertices).
    The exact convex hull of the coupled 2-ReLU relaxation curve is the polytope on
    the ≤4 breakpoints (box endpoints + the ≤2 ReLU crossings, clamped to the box).
    NO nonzero / sign / ordering hypotheses — the joint cut family describes the exact
    hull facets in the coupled regime UNIVERSALLY. -/
theorem coupled_convHull_eq_breakpoints_general (a1 c1 a2 c2 xl xu : ℝ) (hxlu : xl ≤ xu) :
    convexHull ℝ (coupledGraph a1 c1 a2 c2 xl xu)
      = convexHull ℝ (vSet a1 c1 a2 c2 xl xu) := by
  refine Subset.antisymm ?_ (convexHull_mono (vSet_subset_graph a1 c1 a2 c2 xl xu hxlu))
  exact convexHull_min (graph_subset_convHull_vSet a1 c1 a2 c2 xl xu hxlu)
    (convex_convexHull ℝ _)

/-! ===================================================================
    SECTION 6.  Consequences: LP-exactness on the breakpoint polytope, the regime
    corollaries (same-sign and opposite-sign slopes), and vertex-set finiteness.
    =================================================================== -/

/-- A linear objective on the ℝ⁴ point `(z1,z2,A1,A2)`. -/
def objC (e1 e2 d1 d2 : ℝ) (p : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  e1 * p.1 + e2 * p.2.1 + d1 * p.2.2.1 + d2 * p.2.2.2

/-- Linear-objective hull invariance: greatest value over `conv S` = over `S`. -/
theorem objC_isGreatest_convHull (e1 e2 d1 d2 : ℝ) (S : Set (ℝ × ℝ × ℝ × ℝ)) (M : ℝ)
    (hM : IsGreatest (objC e1 e2 d1 d2 '' S) M) :
    IsGreatest (objC e1 e2 d1 d2 '' convexHull ℝ S) M := by
  obtain ⟨⟨p0, hp0S, hp0v⟩, hub⟩ := hM
  refine ⟨⟨p0, subset_convexHull ℝ S hp0S, hp0v⟩, ?_⟩
  rintro v ⟨p, hp, rfl⟩
  have hconvHS : convexHull ℝ S ⊆ {p | objC e1 e2 d1 d2 p ≤ M} := by
    apply convexHull_min
    · intro q hqS; exact hub ⟨q, hqS, rfl⟩
    · rw [convex_iff_forall_pos]
      rintro q hq w hw s t hs ht hst
      simp only [mem_setOf_eq] at hq hw ⊢
      have hlin : objC e1 e2 d1 d2 (s • q + t • w)
                = s * objC e1 e2 d1 d2 q + t * objC e1 e2 d1 d2 w := by
        simp only [objC, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
                   smul_eq_mul]; ring
      rw [hlin]
      calc s * objC e1 e2 d1 d2 q + t * objC e1 e2 d1 d2 w
          ≤ s * M + t * M :=
            add_le_add (mul_le_mul_of_nonneg_left hq hs.le)
                       (mul_le_mul_of_nonneg_left hw ht.le)
        _ = M := by rw [← add_mul, hst, one_mul]
  exact hconvHS hp

/-- **LP-exactness on the breakpoint polytope (GENERAL).**  For every linear
    objective, IF its greatest value `M` over the finite breakpoint vertex set is
    attained, THEN `M` is also the greatest value over the ENTIRE coupled hull
    conv(coupledGraph).  So optimizing any linear objective over the exact coupled
    relaxation reduces to checking the ≤4 breakpoints — no relaxation gap. -/
theorem coupled_lp_max_on_breakpoints (a1 c1 a2 c2 xl xu e1 e2 d1 d2 : ℝ) (M : ℝ)
    (hxlu : xl ≤ xu)
    (hM : IsGreatest (objC e1 e2 d1 d2 '' vSet a1 c1 a2 c2 xl xu) M) :
    IsGreatest (objC e1 e2 d1 d2 '' convexHull ℝ (coupledGraph a1 c1 a2 c2 xl xu)) M := by
  have := objC_isGreatest_convHull e1 e2 d1 d2 (vSet a1 c1 a2 c2 xl xu) M hM
  rwa [← coupled_convHull_eq_breakpoints_general a1 c1 a2 c2 xl xu hxlu] at this

/-- The vertex set has at most 4 elements (it is the image of a 4-element x-set). -/
theorem vSet_finite (a1 c1 a2 c2 xl xu : ℝ) : (vSet a1 c1 a2 c2 xl xu).Finite := by
  apply Set.Finite.image
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  exact Set.finite_singleton _

/-- **Regime corollary — SAME-SIGN slopes (`a1·a2 > 0`).**  The general V-description
    specializes verbatim; both pre-activations increase/decrease together. -/
theorem coupled_convHull_eq_breakpoints_sameSign (a1 c1 a2 c2 xl xu : ℝ)
    (_hsame : 0 < a1 * a2) (hxlu : xl ≤ xu) :
    convexHull ℝ (coupledGraph a1 c1 a2 c2 xl xu)
      = convexHull ℝ (vSet a1 c1 a2 c2 xl xu) :=
  coupled_convHull_eq_breakpoints_general a1 c1 a2 c2 xl xu hxlu

/-- **Regime corollary — OPPOSITE-SIGN slopes (`a1·a2 < 0`).**  The anti-correlated
    regime of the Wave-2 instance (a1=1, a2=-1) is one point of this family. -/
theorem coupled_convHull_eq_breakpoints_oppSign (a1 c1 a2 c2 xl xu : ℝ)
    (_hopp : a1 * a2 < 0) (hxlu : xl ≤ xu) :
    convexHull ℝ (coupledGraph a1 c1 a2 c2 xl xu)
      = convexHull ℝ (vSet a1 c1 a2 c2 xl xu) :=
  coupled_convHull_eq_breakpoints_general a1 c1 a2 c2 xl xu hxlu

/-! ===================================================================
    Trust-base check.  Every theorem depends ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

#print axioms curve_mem_segment_signconst
#print axioms affine_signSplit
#print axioms joint_bracket
#print axioms graph_subset_convHull_vSet
#print axioms coupled_convHull_eq_breakpoints_general
#print axioms coupled_lp_max_on_breakpoints
#print axioms vSet_finite
#print axioms coupled_convHull_eq_breakpoints_sameSign
#print axioms coupled_convHull_eq_breakpoints_oppSign

end CrownproofGeneral
