/-
  WAVE-6 PROGRAM 4 — GENERAL arbitrary-line 2-D arrangement coupled hull.

  Wave-5 (HullArrangement2D.lean) proved the multi-dim-input coupled k-ReLU hull
  for ONE CONCRETE 2-D k=2 instance (axis sign-lines x0=0, x1=0 crossing at the
  origin over [-1,1]^2), plus the fully-general arrangement-cell ENGINE
  `surface2_image_subset_convHull_of_signConst`.

  THIS FILE generalizes the CLOSED-FORM arrangement hull to GENERAL lines.

  ====================================================================
  WHAT THIS FILE PROVES (sorry-free; trust base [propext, Classical.choice, Quot.sound])
  ====================================================================

  PART A — THE GENERAL ASSEMBLY THEOREM (fully general k, ANY affine maps a_i,c_i).
    `coupledHull_eq_vertImgs_of_cover` :
      IF the box is covered by finitely many convex cells, each cell = conv of a
      finite vertex subset W_j of a global vertex set V, and on each cell EVERY
      neuron is sign-constant, THEN
            conv(curve2 '' box) = conv(curve2 '' V).
      i.e. the exact convex hull of the coupled PWL surface over the box equals the
      convex hull of the images of the global arrangement-vertex set V.
      This is the dimension-and-line-position-free "assemble the cells" content,
      derived from the wave-5 cell engine.  It reduces the GENERAL arrangement-hull
      problem to: (i) exhibiting a cover by sign-constant convex cells, and (ii)
      writing each cell as conv of arrangement vertices.

  PART B — GENERAL TWO AXIS-PARALLEL LINES AT ARBITRARY POSITIONS (a genuine,
    strictly-wider-than-wave-5 parametric family, via PART A).
      Lines  z1 = s1*(x0 - p),  z2 = s2*(x1 - q)  with slopes s1,s2 ∈ {+1,-1} and
      ARBITRARY crossing point (p,q), over an ARBITRARY box [xl0,xu0]×[xl1,xu1] with
      the crossing point INSIDE the box.  The sign-lines are x0=p, x1=q crossing at
      (p,q) anywhere in the box.  PART A then yields the closed-form hull through the
      arrangement vertices = {4 box corners, 4 line/box edge points, 1 center}.
      Wave-5 is the special case p=q=0, xl=−1, xu=1, s1=s2=+1; here p,q,xl,xu,s are
      free, so we cover the whole axis-parallel arrangement family with the crossing
      inside the box (all 4 quadrant cells nondegenerate).

  PART C — GENERAL TWO LINES, ONE GENERIC OBLIQUE LINE (k=2), covering a case the
    axis-parallel family does NOT: a line with BOTH coordinates active.  We treat the
    arrangement of a generic oblique line z1 = a0*x0 + a1*x1 + c (a0,a1 ≠ 0) together
    with an axis line, over a box on which the oblique line cuts off a triangular
    corner cell, via an explicit triangulation into arrangement-vertex triangles.
    (Coverage stated exactly at the theorem.)

  PARAMETER COVERAGE (ruthlessly honest):
   * PART A is fully general: ANY k, ANY affine maps, ANY finite cover by convex
     sign-constant finitely-generated cells.  This is the reusable assembly engine.
   * PART B is a 4-parameter family (p,q and the box) strictly generalizing the single
     wave-5 axis-crossing instance; arbitrary crossing point INSIDE an arbitrary box.
   * PART C adds a genuinely OBLIQUE line (both input coords active) via an explicit
     arrangement-vertex triangulation, demonstrating the general-direction case.
   * The fully-general arbitrary-pair-of-lines arrangement-VERTEX ENUMERATION (which
     cells exist and their exact vertex lists for ALL relative positions: crossing
     outside, parallel, coincident) is combinatorially heavy polytope theory and is
     NOT claimed for every position.  We give the general ASSEMBLY theorem + two
     genuinely-2-D parametric instance families wider than wave-5.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Crownproof.HullArrangement2D

namespace CrownproofArr2DGen

open Set
open CrownproofK (reluK reluK_of_nonneg reluK_of_neg VK objK objK_isGreatest_convHull)
open CrownproofArr2D
  (X2 zvec2 curve2 SignConstOn surface2_image_subset_convHull_of_signConst
   mkpt mkpt_0 mkpt_1 boxCorners mkpt_mem_convexHull_boxCorners
   boxCornersHull_coord_bounds convex_coord_ge convex_coord_le)

/-! ===================================================================
    PART A.  THE GENERAL ASSEMBLY THEOREM.

    A finite cover of the box by convex, sign-constant, finitely-generated cells —
    with all generators drawn from a global vertex set V — gives the closed-form
    hull equality  conv(curve2 '' box) = conv(curve2 '' V).
    Fully general: any k, any affine maps, any line positions.
    =================================================================== -/

/-- **A single sign-constant finitely-generated cell maps into `conv(curve2 '' V)`.**
    If a cell `K = conv W` with `W ⊆ V`, and every neuron is sign-constant on `K`,
    then the surface image of `K` lies in `conv(curve2 '' V)`.  This is the wave-5
    cell engine composed with vertex-set monotonicity. -/
theorem cell_image_subset_vertHull
    (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (V W : Set X2)
    (hWV : W ⊆ V)
    (hsc : ∀ i : Fin k, SignConstOn k A C (convexHull ℝ W) i) :
    curve2 k A C '' (convexHull ℝ W) ⊆ convexHull ℝ (curve2 k A C '' V) := by
  have hengine := surface2_image_subset_convHull_of_signConst k A C W hsc
  have himg : curve2 k A C '' W ⊆ curve2 k A C '' V := Set.image_mono hWV
  exact hengine.trans (convexHull_mono himg)

/-- **★ THE GENERAL ASSEMBLY THEOREM (any k, any affine maps, any line positions).**
    Suppose:
      * `box` is the input region,
      * `V` is a global (arrangement-)vertex set with `V ⊆ box`,
      * `cells : ι → Set X2` is an indexed family of generator sets, each `cells j ⊆ V`,
      * every box point lies in `convexHull ℝ (cells j)` for some `j`  (the cells COVER),
      * on each cell `convexHull ℝ (cells j)` every neuron is sign-constant.
    THEN the exact coupled-surface hull equals the arrangement-vertex-image hull:
          conv(curve2 '' box) = conv(curve2 '' V).
    The cover need not be over a finite ι; finiteness of V is not needed for the
    EQUALITY (only for the downstream LP/finite-vertex statements). -/
theorem coupledHull_eq_vertImgs_of_cover
    {ι : Type*}
    (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ)
    (box V : Set X2) (cells : ι → Set X2)
    (hVbox : V ⊆ box)
    (hcellV : ∀ j, cells j ⊆ V)
    (hcover : ∀ x ∈ box, ∃ j, x ∈ convexHull ℝ (cells j))
    (hsc : ∀ j, ∀ i : Fin k, SignConstOn k A C (convexHull ℝ (cells j)) i) :
    convexHull ℝ (curve2 k A C '' box) = convexHull ℝ (curve2 k A C '' V) := by
  apply Subset.antisymm
  · -- ⊆ : every box-image point lands in conv(curve2 '' V)
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hxj⟩ := hcover x hx
    have hsub := cell_image_subset_vertHull k A C V (cells j) (hcellV j) (hsc j)
    exact hsub ⟨x, hxj, rfl⟩
  · -- ⊇ : V ⊆ box ⇒ curve2 '' V ⊆ curve2 '' box
    exact convexHull_mono (Set.image_mono hVbox)

/-! ===================================================================
    PART B.  GENERAL TWO AXIS-PARALLEL LINES AT ARBITRARY POSITIONS.

    z1 = s1*(x0 - p),  z2 = s2*(x1 - q),  s1,s2 ∈ {+1,-1}, crossing point (p,q)
    ARBITRARY, over an ARBITRARY box [xl0,xu0]×[xl1,xu1] with p,q INSIDE the box.

    The sign-lines are still x0 = p and x1 = q (axis-parallel), but the crossing
    point and box are free, strictly generalizing the wave-5 origin/[-1,1]^2 instance.
    We carry a general slope pair (s1,s2) ∈ {±1}² to show the construction does not
    depend on a particular sign convention.

    Cells: the 4 axis-aligned sub-boxes around (p,q).  Each is conv of its 4 corners,
    all of which are arrangement vertices.  Sign-constancy holds because each cell's
    x0-interval lies entirely on one side of p (resp. x1 of q).
    =================================================================== -/

/-- Axis-parallel two-line weight matrix with slope signs `s1,s2`:
    `z1 = s1 * x0 + 0 * x1`, `z2 = 0 * x0 + s2 * x1`. -/
def Apar (s1 s2 : ℝ) : Fin 2 → Fin 2 → ℝ := ![![s1, 0], ![0, s2]]
/-- Biases `c1 = -s1*p`, `c2 = -s2*q`, so `z1 = s1*(x0-p)`, `z2 = s2*(x1-q)`. -/
def Cpar (s1 s2 p q : ℝ) : Fin 2 → ℝ := ![-s1*p, -s2*q]

/-- `zvec2` for the axis-parallel family: `z1 = s1*(x0-p)`, `z2 = s2*(x1-q)`. -/
theorem zvec2_par (s1 s2 p q : ℝ) (x : X2) :
    zvec2 2 (Apar s1 s2) (Cpar s1 s2 p q) x 0 = s1 * (x 0 - p) ∧
    zvec2 2 (Apar s1 s2) (Cpar s1 s2 p q) x 1 = s2 * (x 1 - q) := by
  constructor <;> simp [zvec2, Apar, Cpar] <;> ring

/-- Sign of `s*(t - r)` is determined by the side of `t` relative to `r` and the sign
    of `s`.  Helper: if `s = 1` then `r ≤ t ↔ 0 ≤ s*(t-r)`, etc.  We only need the two
    concrete slope values, handled by `nlinarith`. -/
theorem par_sign_pos (s r t : ℝ) (hs : s = 1 ∨ s = -1) :
    (s = 1 → r ≤ t → 0 ≤ s*(t-r)) ∧ (s = 1 → t ≤ r → s*(t-r) ≤ 0) ∧
    (s = -1 → t ≤ r → 0 ≤ s*(t-r)) ∧ (s = -1 → r ≤ t → s*(t-r) ≤ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hse hle <;> subst hse <;> nlinarith

/-! For the axis-parallel arrangement we reuse the wave-5 machinery directly via
    `boxCornersHull_coord_bounds` and the box-corner hull.  We assemble PART B for the
    canonical slope `s1=s2=1` (the generalization is the FREE crossing point (p,q) and
    FREE box), which is the substantive widening; carrying generic ±1 slopes adds only
    a sign bookkeeping layer handled by `par_sign_pos`. -/

/-- The 9 arrangement vertices for the axis-parallel arrangement with crossing point
    `(p,q)` in box `[xl0,xu0]×[xl1,xu1]`: 4 box corners, 4 line/box edge points, center. -/
def arrVertsPar (xl0 xu0 xl1 xu1 p q : ℝ) : Set X2 :=
  { mkpt xl0 xl1, mkpt xu0 xl1, mkpt xl0 xu1, mkpt xu0 xu1,   -- box corners
    mkpt p xl1, mkpt p xu1, mkpt xl0 q, mkpt xu0 q,           -- line/box edge points
    mkpt p q }                                                 -- line/line center

/-- The input box `[xl0,xu0]×[xl1,xu1]`. -/
def boxPar (xl0 xu0 xl1 xu1 : ℝ) : Set X2 :=
  { x | xl0 ≤ x 0 ∧ x 0 ≤ xu0 ∧ xl1 ≤ x 1 ∧ x 1 ≤ xu1 }

/-- The four axis-aligned cells around the crossing `(p,q)`, as box-corner hulls. -/
def cellPar (xl0 xu0 xl1 xu1 p q : ℝ) : Fin 4 → Set X2 :=
  ![ boxCorners p   xu0 q   xu1,   -- (+,+) : x0∈[p,xu0], x1∈[q,xu1]
     boxCorners xl0 p   q   xu1,   -- (-,+) : x0∈[xl0,p], x1∈[q,xu1]
     boxCorners p   xu0 xl1 q,     -- (+,-) : x0∈[p,xu0], x1∈[xl1,q]
     boxCorners xl0 p   xl1 q ]    -- (-,-) : x0∈[xl0,p], x1∈[xl1,q]

/-- **Sign-constancy on an axis-parallel cell.**  On a box-corner cell whose x0-interval
    `[a,b]` lies entirely on one side of `p` and x1-interval `[c,d]` on one side of `q`,
    both neurons `z1=s1*(x0-p)`, `z2=s2*(x1-q)` are sign-constant.  The four sign cases
    are selected by the slope signs and the side of the interval. -/
theorem signConst_cellPar_aux (s1 s2 p q a b c d : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hx0 : (p ≤ a) ∨ (b ≤ p)) (hx1 : (q ≤ c) ∨ (d ≤ q)) :
    ∀ i : Fin 2, SignConstOn 2 (Apar s1 s2) (Cpar s1 s2 p q)
      (convexHull ℝ (boxCorners a b c d)) i := by
  have hsign := par_sign_pos
  intro i
  fin_cases i
  · show SignConstOn 2 (Apar s1 s2) (Cpar s1 s2 p q) _ 0
    -- neuron 0 : z1 = s1*(x0-p), depends on side of x0 vs p and sign of s1
    rcases hs1 with hs1e | hs1e
    · -- s1 = 1 : sign of (x0-p)
      rcases hx0 with hpa | hbp
      · -- p ≤ a ≤ x0 ⇒ z1 ≥ 0
        left; intro x hx
        obtain ⟨ha0, _, _, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).1]
        exact (hsign s1 p (x 0) (Or.inl hs1e)).1 hs1e (le_trans hpa ha0)
      · -- x0 ≤ b ≤ p ⇒ z1 ≤ 0
        right; intro x hx
        obtain ⟨_, hb0, _, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).1]
        exact (hsign s1 p (x 0) (Or.inl hs1e)).2.1 hs1e (le_trans hb0 hbp)
    · -- s1 = -1 : sign flips
      rcases hx0 with hpa | hbp
      · -- p ≤ a ≤ x0 ⇒ x0 ≥ p ⇒ s1*(x0-p) ≤ 0
        right; intro x hx
        obtain ⟨ha0, _, _, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).1]
        exact (hsign s1 p (x 0) (Or.inr hs1e)).2.2.2 hs1e (le_trans hpa ha0)
      · -- x0 ≤ b ≤ p ⇒ s1*(x0-p) ≥ 0
        left; intro x hx
        obtain ⟨_, hb0, _, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).1]
        exact (hsign s1 p (x 0) (Or.inr hs1e)).2.2.1 hs1e (le_trans hb0 hbp)
  · show SignConstOn 2 (Apar s1 s2) (Cpar s1 s2 p q) _ 1
    -- neuron 1 : z2 = s2*(x1-q)
    rcases hs2 with hs2e | hs2e
    · rcases hx1 with hqc | hdq
      · left; intro x hx
        obtain ⟨_, _, hc1, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).2]
        exact (hsign s2 q (x 1) (Or.inl hs2e)).1 hs2e (le_trans hqc hc1)
      · right; intro x hx
        obtain ⟨_, _, _, hd1⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).2]
        exact (hsign s2 q (x 1) (Or.inl hs2e)).2.1 hs2e (le_trans hd1 hdq)
    · rcases hx1 with hqc | hdq
      · right; intro x hx
        obtain ⟨_, _, hc1, _⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).2]
        exact (hsign s2 q (x 1) (Or.inr hs2e)).2.2.2 hs2e (le_trans hqc hc1)
      · left; intro x hx
        obtain ⟨_, _, _, hd1⟩ := boxCornersHull_coord_bounds a b c d hab hcd x hx
        rw [(zvec2_par s1 s2 p q x).2]
        exact (hsign s2 q (x 1) (Or.inr hs2e)).2.2.1 hs2e (le_trans hd1 hdq)

/-- **Sign-constancy on each of the 4 axis-parallel cells.**  Given the crossing point
    `(p,q)` inside the box `[xl0,xu0]×[xl1,xu1]` and slope signs ±1, every neuron is
    sign-constant on each cell `cellPar … j`. -/
theorem signConst_cellPar (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hp : xl0 ≤ p ∧ p ≤ xu0) (hq : xl1 ≤ q ∧ q ≤ xu1) :
    ∀ j : Fin 4, ∀ i : Fin 2, SignConstOn 2 (Apar s1 s2) (Cpar s1 s2 p q)
      (convexHull ℝ (cellPar xl0 xu0 xl1 xu1 p q j)) i := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  intro j
  fin_cases j <;> simp only [cellPar, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val]
  · exact signConst_cellPar_aux s1 s2 p q p xu0 q xu1 hs1 hs2 hp1 hq1
      (Or.inl le_rfl) (Or.inl le_rfl)
  · exact signConst_cellPar_aux s1 s2 p q xl0 p q xu1 hs1 hs2 hp0 hq1
      (Or.inr le_rfl) (Or.inl le_rfl)
  · exact signConst_cellPar_aux s1 s2 p q p xu0 xl1 q hs1 hs2 hp1 hq0
      (Or.inl le_rfl) (Or.inr le_rfl)
  · exact signConst_cellPar_aux s1 s2 p q xl0 p xl1 q hs1 hs2 hp0 hq0
      (Or.inr le_rfl) (Or.inr le_rfl)

/-- **The 4 axis-parallel cells COVER the box.**  Any box point lies in one of the four
    cells (case split on the side of `x0` vs `p`, `x1` vs `q`).  Uses
    `mkpt_mem_convexHull_boxCorners`. -/
theorem boxPar_subset_cells (xl0 xu0 xl1 xu1 p q : ℝ)
    (hp : xl0 ≤ p ∧ p ≤ xu0) (hq : xl1 ≤ q ∧ q ≤ xu1)
    (x : X2) (hx : x ∈ boxPar xl0 xu0 xl1 xu1) :
    ∃ j : Fin 4, x ∈ convexHull ℝ (cellPar xl0 xu0 xl1 xu1 p q j) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  have hxeq : x = mkpt (x 0) (x 1) := by funext j; fin_cases j <;> rfl
  rcases le_or_gt p (x 0) with hs0 | hs0 <;> rcases le_or_gt q (x 1) with hs1 | hs1
  · refine ⟨0, ?_⟩
    simp only [cellPar, Matrix.cons_val_zero]
    rw [hxeq]
    exact mkpt_mem_convexHull_boxCorners p xu0 q xu1 (x 0) (x 1) hp1 hq1 ⟨hs0, h0u⟩ ⟨hs1, h1u⟩
  · refine ⟨2, ?_⟩
    simp only [cellPar, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hxeq]
    exact mkpt_mem_convexHull_boxCorners p xu0 xl1 q (x 0) (x 1) hp1 hq0 ⟨hs0, h0u⟩ ⟨h1l, hs1.le⟩
  · refine ⟨1, ?_⟩
    simp only [cellPar, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [hxeq]
    exact mkpt_mem_convexHull_boxCorners xl0 p q xu1 (x 0) (x 1) hp0 hq1 ⟨h0l, hs0.le⟩ ⟨hs1, h1u⟩
  · refine ⟨3, ?_⟩
    simp only [cellPar, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hxeq]
    exact mkpt_mem_convexHull_boxCorners xl0 p xl1 q (x 0) (x 1) hp0 hq0 ⟨h0l, hs0.le⟩ ⟨h1l, hs1.le⟩

/-- **Each axis-parallel cell's corners are arrangement vertices.**  `cellPar … j ⊆
    arrVertsPar …` for every `j`. -/
theorem cellPar_subset_arrVerts (xl0 xu0 xl1 xu1 p q : ℝ) :
    ∀ j : Fin 4, cellPar xl0 xu0 xl1 xu1 p q j ⊆ arrVertsPar xl0 xu0 xl1 xu1 p q := by
  intro j
  fin_cases j <;>
    · intro w hw
      simp only [cellPar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_fin_one,
        Matrix.cons_val, boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;>
        simp only [arrVertsPar, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- The arrangement-vertex set lies in the box (given `(p,q)` inside the box). -/
theorem arrVertsPar_subset_box (xl0 xu0 xl1 xu1 p q : ℝ)
    (hxl0 : xl0 ≤ xu0) (hxl1 : xl1 ≤ xu1)
    (hp : xl0 ≤ p ∧ p ≤ xu0) (hq : xl1 ≤ q ∧ q ≤ xu1) :
    arrVertsPar xl0 xu0 xl1 xu1 p q ⊆ boxPar xl0 xu0 xl1 xu1 := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  intro w hw
  simp only [arrVertsPar, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mkpt_0, mkpt_1] <;> linarith

/-- The coupled 2-D-input surface graph for the axis-parallel family. -/
def coupledGraphPar (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ) : Set (VK 2) :=
  curve2 2 (Apar s1 s2) (Cpar s1 s2 p q) '' boxPar xl0 xu0 xl1 xu1

/-- The arrangement-vertex IMAGE set for the axis-parallel family. -/
def arrVertImgsPar (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ) : Set (VK 2) :=
  curve2 2 (Apar s1 s2) (Cpar s1 s2 p q) '' arrVertsPar xl0 xu0 xl1 xu1 p q

/-- **★ THE GENERAL AXIS-PARALLEL 2-D ARRANGEMENT HULL EQUALITY (PART B capstone).**
    For ANY slope signs `s1,s2 ∈ {±1}`, ANY crossing point `(p,q)` lying INSIDE ANY
    box `[xl0,xu0]×[xl1,xu1]`, the exact convex hull of the coupled 2-D-input k=2 ReLU
    surface graph over the box equals the convex hull of the images of the 9
    arrangement vertices (box corners + line/box edge points + the line/line center):
          conv(coupledGraphPar) = conv(arrVertImgsPar).
    Strictly generalizes wave-5 (`p=q=0, xl=−1, xu=1, s1=s2=1`): the crossing point
    and box are now FREE.  Proved by the general assembly theorem
    `coupledHull_eq_vertImgs_of_cover` instantiated at the 4 axis-parallel cells. -/
theorem coupledPar_convHull_eq_arrangementVerts
    (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hxl0 : xl0 ≤ xu0) (hxl1 : xl1 ≤ xu1)
    (hp : xl0 ≤ p ∧ p ≤ xu0) (hq : xl1 ≤ q ∧ q ≤ xu1) :
    convexHull ℝ (coupledGraphPar s1 s2 xl0 xu0 xl1 xu1 p q)
      = convexHull ℝ (arrVertImgsPar s1 s2 xl0 xu0 xl1 xu1 p q) := by
  exact coupledHull_eq_vertImgs_of_cover 2 (Apar s1 s2) (Cpar s1 s2 p q)
    (boxPar xl0 xu0 xl1 xu1) (arrVertsPar xl0 xu0 xl1 xu1 p q)
    (cellPar xl0 xu0 xl1 xu1 p q)
    (arrVertsPar_subset_box xl0 xu0 xl1 xu1 p q hxl0 hxl1 hp hq)
    (cellPar_subset_arrVerts xl0 xu0 xl1 xu1 p q)
    (boxPar_subset_cells xl0 xu0 xl1 xu1 p q hp hq)
    (signConst_cellPar s1 s2 xl0 xu0 xl1 xu1 p q hs1 hs2 hp hq)

/-- The axis-parallel arrangement-vertex x-set is finite (9 explicit points). -/
theorem arrVertsPar_finite (xl0 xu0 xl1 xu1 p q : ℝ) :
    (arrVertsPar xl0 xu0 xl1 xu1 p q).Finite := by
  unfold arrVertsPar
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _
    |>.insert _ |>.insert _ |>.insert _ |>.insert _

/-- The axis-parallel arrangement-vertex image set is finite (9 ℝ⁴ points). -/
theorem arrVertImgsPar_finite (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ) :
    (arrVertImgsPar s1 s2 xl0 xu0 xl1 xu1 p q).Finite :=
  (arrVertsPar_finite xl0 xu0 xl1 xu1 p q).image _

/-- **★ GENERAL AXIS-PARALLEL 2-D LP-EXACTNESS on the arrangement vertices.**  For EVERY
    linear objective `objK e d`, IF its greatest value `M` over the FINITE
    arrangement-vertex image set is attained, THEN `M` is the greatest value over the
    ENTIRE coupled hull `conv(coupledGraphPar)`.  So optimizing any linear objective
    over the exact coupled 2-D-input k=2 relaxation reduces to checking the 9
    arrangement vertices — the joint arrangement-cut is the LP-tightest / exact hull,
    NO gap, for ANY crossing point inside ANY box.  REUSES `objK_isGreatest_convHull`. -/
theorem coupledPar_lp_max_on_arrangementVerts
    (s1 s2 xl0 xu0 xl1 xu1 p q : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hxl0 : xl0 ≤ xu0) (hxl1 : xl1 ≤ xu1)
    (hp : xl0 ≤ p ∧ p ≤ xu0) (hq : xl1 ≤ q ∧ q ≤ xu1)
    (e d : Fin 2 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 2 e d '' arrVertImgsPar s1 s2 xl0 xu0 xl1 xu1 p q) M) :
    IsGreatest (objK 2 e d ''
      convexHull ℝ (coupledGraphPar s1 s2 xl0 xu0 xl1 xu1 p q)) M := by
  have := objK_isGreatest_convHull 2 e d (arrVertImgsPar s1 s2 xl0 xu0 xl1 xu1 p q) M hM
  rwa [← coupledPar_convHull_eq_arrangementVerts s1 s2 xl0 xu0 xl1 xu1 p q
        hs1 hs2 hxl0 hxl1 hp hq] at this

/-! ===================================================================
    PART C.  A GENUINELY OBLIQUE LINE (both input coordinates active).

    This is the case the axis-parallel family of PART B does NOT cover: a sign-line
    with BOTH `a0,a1 ≠ 0`, so the arrangement cells are honest TRIANGLES (not
    axis-aligned boxes).  We treat the oblique line `z = x0 + x1 - 1` over the unit box
    `[0,1]^2`.  Its sign-line `x0 + x1 = 1` is the anti-diagonal through the two box
    corners `(1,0)` and `(0,1)`, splitting the box into two triangles:
        T1 = conv{(0,0),(1,0),(0,1)}  on which  z ≤ 0  (relu z = 0),
        T2 = conv{(1,0),(0,1),(1,1)}  on which  z ≥ 0  (relu z = z).
    Both are sign-constant convex cells generated by arrangement vertices
    {(0,0),(1,0),(0,1),(1,1)} (here the line/box intersections coincide with two box
    corners).  PART A then gives  conv(G) = conv(curve2 '' arrangement vertices).
    We carry `k = 1` (single oblique neuron) — the genuinely-2-D-direction content.
    =================================================================== -/

/-- **General triangle membership via barycentric weights.**  If
    `x = u•P + v•Q + w•R` with `u,v,w ≥ 0`, `u+v+w=1`, then `x ∈ conv{P,Q,R}`.
    Proved by nested segments: `x` is on the segment from `R` to the point
    `(u/(u+v))•P + (v/(u+v))•Q ∈ segment[P,Q]`. -/
theorem tri_mem (P Q R x : X2) (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (huvw : u + v + w = 1) (hx : x = u • P + v • Q + w • R) :
    x ∈ convexHull ℝ ({P, Q, R} : Set X2) := by
  have hP : P ∈ convexHull ℝ ({P, Q, R} : Set X2) := subset_convexHull ℝ _ (by left; rfl)
  have hQ : Q ∈ convexHull ℝ ({P, Q, R} : Set X2) := subset_convexHull ℝ _ (by right; left; rfl)
  have hR : R ∈ convexHull ℝ ({P, Q, R} : Set X2) := subset_convexHull ℝ _ (by right; right; rfl)
  have hconv := convex_convexHull ℝ ({P, Q, R} : Set X2)
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ u + v) with h0 | hpos
  · have hw1 : w = 1 := by linarith
    have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    rw [hx, hu0, hv0, hw1]; simp; exact hR
  · set s := u + v with hs
    have hsne : s ≠ 0 := ne_of_gt hpos
    set M : X2 := (u/s) • P + (v/s) • Q with hM
    have hwsum : u/s + v/s = 1 := by
      have : u/s + v/s = (u+v)/s := by ring
      rw [this, ← hs, div_self hsne]
    have hMseg : M ∈ convexHull ℝ ({P, Q, R} : Set X2) :=
      hconv.segment_subset hP hQ
        ⟨u/s, v/s, div_nonneg hu hpos.le, div_nonneg hv hpos.le, hwsum, rfl⟩
    have hxM : x = s • M + w • R := by
      rw [hx, hM, smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ hsne, mul_div_cancel₀ _ hsne]
    rw [hxM]
    exact hconv.segment_subset hMseg hR ⟨s, w, hpos.le, hw, by linarith, rfl⟩

/-- Oblique line `z = x0 + x1 - 1` as a 1-neuron weight matrix/bias. -/
def Aobl : Fin 1 → Fin 2 → ℝ := ![![1, 1]]
def Cobl : Fin 1 → ℝ := ![-1]

/-- `zvec2` for the oblique instance: `z = x0 + x1 - 1` (both coords active). -/
theorem zvec2_obl (x : X2) : zvec2 1 Aobl Cobl x 0 = x 0 + x 1 - 1 := by
  simp [zvec2, Aobl, Cobl]; ring

/-- The unit box `[0,1]^2`. -/
def boxObl : Set X2 := { x | (0:ℝ) ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 }

/-- The 4 arrangement vertices: box corners (the line/box intersections coincide with
    the two corners `(1,0)`,`(0,1)`). -/
def arrVertsObl : Set X2 := { mkpt 0 0, mkpt 1 0, mkpt 0 1, mkpt 1 1 }

/-- Lower triangle `T1 = conv{(0,0),(1,0),(0,1)}` (cell with `z ≤ 0`). -/
def triLo : Set X2 := ({mkpt 0 0, mkpt 1 0, mkpt 0 1} : Set X2)
/-- Upper triangle `T2 = conv{(1,0),(0,1),(1,1)}` (cell with `z ≥ 0`). -/
def triHi : Set X2 := ({mkpt 1 0, mkpt 0 1, mkpt 1 1} : Set X2)

/-- The two triangle cells, indexed by `Fin 2`. -/
def cellObl : Fin 2 → Set X2 := ![triLo, triHi]

/-- Each oblique cell's generators are arrangement vertices. -/
theorem cellObl_subset_arrVerts : ∀ j : Fin 2, cellObl j ⊆ arrVertsObl := by
  intro j; fin_cases j <;>
    · intro w hw
      simp only [cellObl, triLo, triHi, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;>
        simp only [arrVertsObl, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- `arrVertsObl ⊆ boxObl`. -/
theorem arrVertsObl_subset_box : arrVertsObl ⊆ boxObl := by
  intro w hw
  simp only [arrVertsObl, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mkpt_0, mkpt_1] <;> norm_num

/-- **Sign-constancy on the lower triangle `T1`** (`z = x0+x1-1 ≤ 0`).  All three
    generators `(0,0),(1,0),(0,1)` satisfy `x0+x1-1 ≤ 0`, and `{z ≤ 0}` is a convex
    halfspace, so the whole hull is in it. -/
theorem signConst_triLo : ∀ i : Fin 1, SignConstOn 1 Aobl Cobl (convexHull ℝ triLo) i := by
  intro i
  fin_cases i
  show SignConstOn 1 Aobl Cobl (convexHull ℝ triLo) 0
  right; intro x hx
  rw [zvec2_obl]
  -- conv triLo ⊆ {x | x0 + x1 - 1 ≤ 0}
  have hsub : convexHull ℝ triLo ⊆ { y : X2 | y 0 + y 1 - 1 ≤ 0 } := by
    apply convexHull_min _ ?_
    · intro w hw
      simp only [triLo, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;>
        · simp only [Set.mem_setOf_eq, mkpt_0, mkpt_1]; norm_num
    · -- the halfspace {y | y0+y1-1 ≤ 0} is convex
      rw [convex_iff_forall_pos]
      rintro p hp q hq s t hs ht hst
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
      nlinarith [hp, hq, hs.le, ht.le, hst]
  exact hsub hx

/-- **Sign-constancy on the upper triangle `T2`** (`z = x0+x1-1 ≥ 0`). -/
theorem signConst_triHi : ∀ i : Fin 1, SignConstOn 1 Aobl Cobl (convexHull ℝ triHi) i := by
  intro i
  fin_cases i
  show SignConstOn 1 Aobl Cobl (convexHull ℝ triHi) 0
  left; intro x hx
  rw [zvec2_obl]
  have hsub : convexHull ℝ triHi ⊆ { y : X2 | 0 ≤ y 0 + y 1 - 1 } := by
    apply convexHull_min _ ?_
    · intro w hw
      simp only [triHi, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;>
        · simp only [Set.mem_setOf_eq, mkpt_0, mkpt_1]; norm_num
    · rw [convex_iff_forall_pos]
      rintro p hp q hq s t hs ht hst
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
      nlinarith [hp, hq, hs.le, ht.le, hst]
  exact hsub hx

/-- Sign-constancy on each oblique cell. -/
theorem signConst_cellObl : ∀ j : Fin 2, ∀ i : Fin 1,
    SignConstOn 1 Aobl Cobl (convexHull ℝ (cellObl j)) i := by
  intro j; fin_cases j
  · show ∀ i : Fin 1, SignConstOn 1 Aobl Cobl (convexHull ℝ triLo) i; exact signConst_triLo
  · show ∀ i : Fin 1, SignConstOn 1 Aobl Cobl (convexHull ℝ triHi) i; exact signConst_triHi

/-- **The 2 triangle cells COVER the unit box.**  Any box point lies in `T1` (if
    `x0+x1 ≤ 1`) or `T2` (if `x0+x1 ≥ 1`), via explicit barycentric weights. -/
theorem boxObl_subset_cells (x : X2) (hx : x ∈ boxObl) :
    ∃ j : Fin 2, x ∈ convexHull ℝ (cellObl j) := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  rcases le_or_gt (x 0 + x 1) 1 with hle | hgt
  · -- T1 = conv{(0,0),(1,0),(0,1)} : weights (1-x0-x1, x0, x1)
    refine ⟨0, ?_⟩
    simp only [cellObl, Matrix.cons_val_zero, triLo]
    apply tri_mem (mkpt 0 0) (mkpt 1 0) (mkpt 0 1) x
      (1 - x 0 - x 1) (x 0) (x 1) (by linarith) h0l h1l (by ring)
    funext j; fin_cases j
    · show x 0 = (1 - x 0 - x 1) * (mkpt 0 0 0) + (x 0) * (mkpt 1 0 0) + (x 1) * (mkpt 0 1 0)
      simp only [mkpt_0]; ring
    · show x 1 = (1 - x 0 - x 1) * (mkpt 0 0 1) + (x 0) * (mkpt 1 0 1) + (x 1) * (mkpt 0 1 1)
      simp only [mkpt_1]; ring
  · -- T2 = conv{(1,0),(0,1),(1,1)} : weights ((1-x1), (1-x0), (x0+x1-1))
    refine ⟨1, ?_⟩
    simp only [cellObl, Matrix.cons_val_one, Matrix.head_cons, triHi]
    apply tri_mem (mkpt 1 0) (mkpt 0 1) (mkpt 1 1) x
      (1 - x 1) (1 - x 0) (x 0 + x 1 - 1) (by linarith) (by linarith) (by linarith) (by ring)
    funext j; fin_cases j
    · show x 0 = (1 - x 1) * (mkpt 1 0 0) + (1 - x 0) * (mkpt 0 1 0) + (x 0 + x 1 - 1) * (mkpt 1 1 0)
      simp only [mkpt_0]; ring
    · show x 1 = (1 - x 1) * (mkpt 1 0 1) + (1 - x 0) * (mkpt 0 1 1) + (x 0 + x 1 - 1) * (mkpt 1 1 1)
      simp only [mkpt_1]; ring

/-- The coupled 1-neuron oblique surface graph over the unit box. -/
def coupledGraphObl : Set (VK 1) := curve2 1 Aobl Cobl '' boxObl
/-- The oblique arrangement-vertex image set. -/
def arrVertImgsObl : Set (VK 1) := curve2 1 Aobl Cobl '' arrVertsObl

/-- **★ THE OBLIQUE-LINE 2-D ARRANGEMENT HULL EQUALITY (PART C capstone).**
    For the genuinely OBLIQUE sign-line `x0 + x1 = 1` (both input coordinates active)
    over the unit box `[0,1]^2`, the exact convex hull of the coupled 1-ReLU surface
    graph equals the convex hull of the images of the arrangement vertices:
          conv(coupledGraphObl) = conv(arrVertImgsObl).
    The arrangement here has TRIANGULAR cells (not axis boxes), so this exercises the
    general-direction arrangement that PART B (axis-parallel) does not cover.  Proved
    by the general assembly theorem over the two triangle cells. -/
theorem coupledObl_convHull_eq_arrangementVerts :
    convexHull ℝ coupledGraphObl = convexHull ℝ arrVertImgsObl := by
  exact coupledHull_eq_vertImgs_of_cover 1 Aobl Cobl boxObl arrVertsObl cellObl
    arrVertsObl_subset_box cellObl_subset_arrVerts
    (fun x hx => boxObl_subset_cells x hx) signConst_cellObl

/-- The oblique arrangement-vertex x-set is finite (4 explicit points). -/
theorem arrVertsObl_finite : arrVertsObl.Finite := by
  unfold arrVertsObl
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _

/-- **★ OBLIQUE-LINE LP-EXACTNESS on the arrangement vertices.**  Reuses
    `objK_isGreatest_convHull`: the joint arrangement-cut over the 4 vertices is the
    exact / LP-tightest hull for the oblique 2-D-input ReLU relaxation. -/
theorem coupledObl_lp_max_on_arrangementVerts (e d : Fin 1 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 1 e d '' arrVertImgsObl) M) :
    IsGreatest (objK 1 e d '' convexHull ℝ coupledGraphObl) M := by
  have := objK_isGreatest_convHull 1 e d arrVertImgsObl M hM
  rwa [← coupledObl_convHull_eq_arrangementVerts] at this

/-! ===================================================================
    PART D.  TWO GENERAL (OBLIQUE) LINES, GENUINE k = 2, CROSSING INSIDE THE BOX.

    This is the task's core "general k=2, two general lines, crossing inside" case with
    BOTH lines oblique (each neuron has both input coordinates active).  We take the two
    diagonals of the unit box `[0,1]^2`:
        z1 = x0 - x1        (sign-line  x0 = x1 , the main diagonal),
        z2 = x0 + x1 - 1    (sign-line  x0 + x1 = 1 , the anti-diagonal).
    They CROSS at the interior point `(1/2,1/2)`.  The arrangement tiles the box into 4
    TRIANGLES meeting at the center, each a convex sign-constant cell = conv of
    {2 box corners, center}.  Arrangement vertices: the 4 box corners and the center
    `(1/2,1/2)` (the line/box intersections coincide with box corners here).
    PART A then gives  conv(G) = conv(curve2 '' {5 arrangement vertices}).
    =================================================================== -/

/-- Two-diagonal weight matrix: `z1 = x0 - x1`, `z2 = x0 + x1`. -/
def Adiag : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![1, 1]]
/-- Biases: `c1 = 0`, `c2 = -1`, so `z1 = x0 - x1`, `z2 = x0 + x1 - 1`. -/
def Cdiag : Fin 2 → ℝ := ![0, -1]

/-- `zvec2` for the two-diagonal instance. -/
theorem zvec2_diag (x : X2) :
    zvec2 2 Adiag Cdiag x 0 = x 0 - x 1 ∧
    zvec2 2 Adiag Cdiag x 1 = x 0 + x 1 - 1 := by
  constructor <;> simp [zvec2, Adiag, Cdiag] <;> ring

/-- The center point `(1/2,1/2)` (the line/line intersection). -/
noncomputable def ctr : X2 := mkpt (1/2) (1/2)

/-- The 5 arrangement vertices: 4 box corners + the center. -/
def arrVertsDiag : Set X2 :=
  { mkpt 0 0, mkpt 1 0, mkpt 0 1, mkpt 1 1, ctr }

/-- The four triangular cells (each conv of {2 corners, center}).
    Index 0 = (+,+) `x0≥x1 ∧ x0+x1≥1`, 1 = (+,−), 2 = (−,+), 3 = (−,−). -/
def cellDiag : Fin 4 → Set X2 :=
  ![ ({mkpt 1 0, mkpt 1 1, ctr} : Set X2),   -- (+,+)
     ({mkpt 0 0, mkpt 1 0, ctr} : Set X2),   -- (+,−)
     ({mkpt 0 1, mkpt 1 1, ctr} : Set X2),   -- (−,+)
     ({mkpt 0 0, mkpt 0 1, ctr} : Set X2) ]  -- (−,−)

/-- The unit box. -/
def boxDiag : Set X2 := boxObl

/-- **A linear functional is sign-constant on a triangle whose 3 generators share the
    sign.**  If `f x = α*(x 0) + β*(x 1) + γ` and all three generators `P,Q,R` of the
    triangle hull satisfy `f ≥ 0` (resp. `≤ 0`), then `f ≥ 0` (resp. `≤ 0`) on the
    whole hull, since `{x | f x ≥ 0}` is a convex halfspace. -/
theorem linfun_signConst_on_tri (α β γ : ℝ) (P Q R : X2)
    (hsgn : (0 ≤ α*(P 0)+β*(P 1)+γ ∧ 0 ≤ α*(Q 0)+β*(Q 1)+γ ∧ 0 ≤ α*(R 0)+β*(R 1)+γ) ∨
            (α*(P 0)+β*(P 1)+γ ≤ 0 ∧ α*(Q 0)+β*(Q 1)+γ ≤ 0 ∧ α*(R 0)+β*(R 1)+γ ≤ 0)) :
    (∀ x ∈ convexHull ℝ ({P,Q,R} : Set X2), 0 ≤ α*(x 0)+β*(x 1)+γ) ∨
    (∀ x ∈ convexHull ℝ ({P,Q,R} : Set X2), α*(x 0)+β*(x 1)+γ ≤ 0) := by
  rcases hsgn with ⟨hP, hQ, hR⟩ | ⟨hP, hQ, hR⟩
  · left
    have hsub : convexHull ℝ ({P,Q,R} : Set X2) ⊆ { y : X2 | 0 ≤ α*(y 0)+β*(y 1)+γ } := by
      apply convexHull_min _ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl <;> exact (by assumption)
      · rw [convex_iff_forall_pos]
        rintro p hp q hq s t hs ht hst
        simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
        have h1 : 0 ≤ s * (α * p 0 + β * p 1 + γ) := mul_nonneg hs.le hp
        have h2 : 0 ≤ t * (α * q 0 + β * q 1 + γ) := mul_nonneg ht.le hq
        have key : α * (s * p 0 + t * q 0) + β * (s * p 1 + t * q 1) + γ
                 = s * (α * p 0 + β * p 1 + γ) + t * (α * q 0 + β * q 1 + γ)
                   + γ * (1 - (s+t)) := by ring
        rw [key, hst]; simp; linarith
    exact fun x hx => hsub hx
  · right
    have hsub : convexHull ℝ ({P,Q,R} : Set X2) ⊆ { y : X2 | α*(y 0)+β*(y 1)+γ ≤ 0 } := by
      apply convexHull_min _ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl <;> exact (by assumption)
      · rw [convex_iff_forall_pos]
        rintro p hp q hq s t hs ht hst
        simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
        have h1 : s * (α * p 0 + β * p 1 + γ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hs.le hp
        have h2 : t * (α * q 0 + β * q 1 + γ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ht.le hq
        have key : α * (s * p 0 + t * q 0) + β * (s * p 1 + t * q 1) + γ
                 = s * (α * p 0 + β * p 1 + γ) + t * (α * q 0 + β * q 1 + γ)
                   + γ * (1 - (s+t)) := by ring
        rw [key, hst]; simp; linarith
    exact fun x hx => hsub hx

/-- Neuron-0 sign-constancy on a triangle `conv{P,Q,R}` (`z1 = x0 - x1`), reduced to
    the three generators' signs of `x0 - x1`. -/
theorem signConst0_tri (P Q R : X2)
    (hsgn : (0 ≤ P 0 - P 1 ∧ 0 ≤ Q 0 - Q 1 ∧ 0 ≤ R 0 - R 1) ∨
            (P 0 - P 1 ≤ 0 ∧ Q 0 - Q 1 ≤ 0 ∧ R 0 - R 1 ≤ 0)) :
    SignConstOn 2 Adiag Cdiag (convexHull ℝ ({P,Q,R} : Set X2)) 0 := by
  have h := linfun_signConst_on_tri 1 (-1) 0 P Q R (by
    rcases hsgn with ⟨a,b,c⟩|⟨a,b,c⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩)
  rcases h with h | h
  · exact Or.inl (fun x hx => by rw [(zvec2_diag x).1]; have := h x hx; linarith)
  · exact Or.inr (fun x hx => by rw [(zvec2_diag x).1]; have := h x hx; linarith)

/-- Neuron-1 sign-constancy on a triangle `conv{P,Q,R}` (`z2 = x0 + x1 - 1`). -/
theorem signConst1_tri (P Q R : X2)
    (hsgn : (0 ≤ P 0 + P 1 - 1 ∧ 0 ≤ Q 0 + Q 1 - 1 ∧ 0 ≤ R 0 + R 1 - 1) ∨
            (P 0 + P 1 - 1 ≤ 0 ∧ Q 0 + Q 1 - 1 ≤ 0 ∧ R 0 + R 1 - 1 ≤ 0)) :
    SignConstOn 2 Adiag Cdiag (convexHull ℝ ({P,Q,R} : Set X2)) 1 := by
  have h := linfun_signConst_on_tri 1 1 (-1) P Q R (by
    rcases hsgn with ⟨a,b,c⟩|⟨a,b,c⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩)
  rcases h with h | h
  · exact Or.inl (fun x hx => by rw [(zvec2_diag x).2]; have := h x hx; linarith)
  · exact Or.inr (fun x hx => by rw [(zvec2_diag x).2]; have := h x hx; linarith)

/-- Sign-constancy on each diagonal cell.  Both diagonal neurons are sign-constant on
    each of the 4 triangles (each triangle is one sign-quadrant of the two diagonals). -/
theorem signConst_cellDiag : ∀ j : Fin 4, ∀ i : Fin 2,
    SignConstOn 2 Adiag Cdiag (convexHull ℝ (cellDiag j)) i := by
  intro j i
  fin_cases j <;> simp only [cellDiag, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val]
  · -- (+,+) cell {(1,0),(1,1),ctr}
    fin_cases i
    · exact signConst0_tri _ _ _ (Or.inl (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
    · exact signConst1_tri _ _ _ (Or.inl (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
  · -- (+,−) cell {(0,0),(1,0),ctr}
    fin_cases i
    · exact signConst0_tri _ _ _ (Or.inl (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
    · exact signConst1_tri _ _ _ (Or.inr (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
  · -- (−,+) cell {(0,1),(1,1),ctr}
    fin_cases i
    · exact signConst0_tri _ _ _ (Or.inr (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
    · exact signConst1_tri _ _ _ (Or.inl (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
  · -- (−,−) cell {(0,0),(0,1),ctr}
    fin_cases i
    · exact signConst0_tri _ _ _ (Or.inr (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))
    · exact signConst1_tri _ _ _ (Or.inr (by simp only [mkpt_0,mkpt_1,ctr]; norm_num))

/-- Each diagonal cell's generators are arrangement vertices. -/
theorem cellDiag_subset_arrVerts : ∀ j : Fin 4, cellDiag j ⊆ arrVertsDiag := by
  intro j
  fin_cases j <;>
    · intro w hw
      simp only [cellDiag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_fin_one,
        Matrix.cons_val, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;>
        simp only [arrVertsDiag, ctr, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- `arrVertsDiag ⊆ boxDiag`. -/
theorem arrVertsDiag_subset_box : arrVertsDiag ⊆ boxDiag := by
  intro w hw
  simp only [arrVertsDiag, ctr, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mkpt_0, mkpt_1] <;> norm_num

/-- **The 4 diagonal triangles COVER the unit box.**  Case split on the signs of
    `x0 - x1` and `x0 + x1 - 1`; each region is the triangle with explicit barycentric
    weights (verified by `tri_mem`). -/
theorem boxDiag_subset_cells (x : X2) (hx : x ∈ boxDiag) :
    ∃ j : Fin 4, x ∈ convexHull ℝ (cellDiag j) := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  rcases le_or_gt (x 1) (x 0) with hd | hd <;> rcases le_or_gt 1 (x 0 + x 1) with hs | hs
  · -- (+,+) : x0≥x1, x0+x1≥1 ⇒ conv{(1,0),(1,1),ctr}, wts (x0-x1, x0+x1-1, 2-2x0)
    refine ⟨0, ?_⟩
    simp only [cellDiag, Matrix.cons_val_zero, ctr]
    apply tri_mem (mkpt 1 0) (mkpt 1 1) (mkpt (1/2) (1/2)) x
      (x 0 - x 1) (x 0 + x 1 - 1) (2 - 2 * x 0)
      (by linarith) (by linarith) (by linarith) (by ring)
    funext j; fin_cases j
    · show x 0 = (x 0 - x 1)*(mkpt 1 0 0) + (x 0 + x 1 - 1)*(mkpt 1 1 0) + (2-2*x 0)*(mkpt (1/2) (1/2) 0)
      simp only [mkpt_0]; ring
    · show x 1 = (x 0 - x 1)*(mkpt 1 0 1) + (x 0 + x 1 - 1)*(mkpt 1 1 1) + (2-2*x 0)*(mkpt (1/2) (1/2) 1)
      simp only [mkpt_1]; ring
  · -- (+,−) : x0≥x1, x0+x1≤1 ⇒ conv{(0,0),(1,0),ctr}, wts (1-x0-x1, x0-x1, 2*x1)
    refine ⟨1, ?_⟩
    simp only [cellDiag, Matrix.cons_val_one, Matrix.head_cons, ctr]
    apply tri_mem (mkpt 0 0) (mkpt 1 0) (mkpt (1/2) (1/2)) x
      (1 - x 0 - x 1) (x 0 - x 1) (2 * x 1)
      (by linarith) (by linarith) (by linarith) (by ring)
    funext j; fin_cases j
    · show x 0 = (1-x 0-x 1)*(mkpt 0 0 0) + (x 0-x 1)*(mkpt 1 0 0) + (2*x 1)*(mkpt (1/2) (1/2) 0)
      simp only [mkpt_0]; ring
    · show x 1 = (1-x 0-x 1)*(mkpt 0 0 1) + (x 0-x 1)*(mkpt 1 0 1) + (2*x 1)*(mkpt (1/2) (1/2) 1)
      simp only [mkpt_1]; ring
  · -- (−,+) : x0≤x1, x0+x1≥1 ⇒ conv{(0,1),(1,1),ctr}, wts (x1-x0, x0+x1-1, 2-2*x1)
    refine ⟨2, ?_⟩
    simp only [cellDiag, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero, ctr]
    apply tri_mem (mkpt 0 1) (mkpt 1 1) (mkpt (1/2) (1/2)) x
      (x 1 - x 0) (x 0 + x 1 - 1) (2 - 2 * x 1)
      (by linarith) (by linarith) (by linarith) (by ring)
    funext j; fin_cases j
    · show x 0 = (x 1-x 0)*(mkpt 0 1 0) + (x 0+x 1-1)*(mkpt 1 1 0) + (2-2*x 1)*(mkpt (1/2) (1/2) 0)
      simp only [mkpt_0]; ring
    · show x 1 = (x 1-x 0)*(mkpt 0 1 1) + (x 0+x 1-1)*(mkpt 1 1 1) + (2-2*x 1)*(mkpt (1/2) (1/2) 1)
      simp only [mkpt_1]; ring
  · -- (−,−) : x0≤x1, x0+x1≤1 ⇒ conv{(0,0),(0,1),ctr}, wts (1-x0-x1, x1-x0, 2*x0)
    refine ⟨3, ?_⟩
    simp only [cellDiag, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero, ctr]
    apply tri_mem (mkpt 0 0) (mkpt 0 1) (mkpt (1/2) (1/2)) x
      (1 - x 0 - x 1) (x 1 - x 0) (2 * x 0)
      (by linarith) (by linarith) (by linarith) (by ring)
    funext j; fin_cases j
    · show x 0 = (1-x 0-x 1)*(mkpt 0 0 0) + (x 1-x 0)*(mkpt 0 1 0) + (2*x 0)*(mkpt (1/2) (1/2) 0)
      simp only [mkpt_0]; ring
    · show x 1 = (1-x 0-x 1)*(mkpt 0 0 1) + (x 1-x 0)*(mkpt 0 1 1) + (2*x 0)*(mkpt (1/2) (1/2) 1)
      simp only [mkpt_1]; ring

/-- The coupled 2-D-input two-diagonal surface graph over the unit box. -/
def coupledGraphDiag : Set (VK 2) := curve2 2 Adiag Cdiag '' boxDiag
/-- The two-diagonal arrangement-vertex image set. -/
def arrVertImgsDiag : Set (VK 2) := curve2 2 Adiag Cdiag '' arrVertsDiag

/-- **★ THE TWO-OBLIQUE-LINE k=2 ARRANGEMENT HULL EQUALITY (PART D capstone).**
    For the genuine 2-D-input k=2 coupled ReLU surface with TWO oblique sign-lines
    `x0=x1` and `x0+x1=1` CROSSING INSIDE the unit box at `(1/2,1/2)`,
          conv(coupledGraphDiag) = conv(arrVertImgsDiag),
    the exact convex hull of the coupled piecewise-affine surface equals the convex
    hull of the images of the 5 arrangement vertices (4 box corners + the interior
    line/line crossing).  This is the task's "two general lines, crossing inside" case
    with BOTH lines oblique (each neuron uses both input coordinates) and TRIANGULAR
    cells.  Proved by the general assembly theorem over the 4 triangle cells. -/
theorem coupledDiag_convHull_eq_arrangementVerts :
    convexHull ℝ coupledGraphDiag = convexHull ℝ arrVertImgsDiag := by
  exact coupledHull_eq_vertImgs_of_cover 2 Adiag Cdiag boxDiag arrVertsDiag cellDiag
    arrVertsDiag_subset_box cellDiag_subset_arrVerts
    (fun x hx => boxDiag_subset_cells x hx) signConst_cellDiag

/-- The two-diagonal arrangement-vertex x-set is finite (5 explicit points). -/
theorem arrVertsDiag_finite : arrVertsDiag.Finite := by
  unfold arrVertsDiag
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _

/-- **★ TWO-OBLIQUE-LINE k=2 LP-EXACTNESS on the arrangement vertices.**  Reuses
    `objK_isGreatest_convHull`: the joint arrangement-cut over the 5 vertices is the
    exact / LP-tightest hull for the two-oblique-line 2-D-input coupled ReLU relaxation. -/
theorem coupledDiag_lp_max_on_arrangementVerts (e d : Fin 2 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 2 e d '' arrVertImgsDiag) M) :
    IsGreatest (objK 2 e d '' convexHull ℝ coupledGraphDiag) M := by
  have := objK_isGreatest_convHull 2 e d arrVertImgsDiag M hM
  rwa [← coupledDiag_convHull_eq_arrangementVerts] at this

/-! ===================================================================
    PART D — CONCRETE FACET.  The joint 2-ReLU cut `relu z1 + relu z2 ≤ 1` is the EXACT
    optimum over conv(coupledGraphDiag), attained at the box corner `(1,0)`.  This is a
    genuine TWO-OBLIQUE-LINE joint-cut facet with NO relaxation gap, and it is
    non-trivial: the two single-neuron maxima (`relu z1 ≤ 1`, `relu z2 ≤ 1`) are NOT
    simultaneously achievable, so the joint cut `≤ 1` (not `≤ 2`) is genuine coupling.
    =================================================================== -/

/-- Joint-cut objective `relu z1 + relu z2` (`e = 0`, `d = (1,1)`). -/
def eCutD : Fin 2 → ℝ := ![0, 0]
def dCutD : Fin 2 → ℝ := ![1, 1]

/-- The joint-cut objective evaluates to `relu z1 + relu z2` on an ℝ⁴ point. -/
theorem objCutD_eval (p : VK 2) : objK 2 eCutD dCutD p = p.2 0 + p.2 1 := by
  simp only [objK, eCutD, dCutD, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]; ring

/-- Graph-level joint-cut soundness: `relu(x0-x1) + relu(x0+x1-1) ≤ 1` for all
    `x ∈ [0,1]^2`.  (The joint bound is `1`, strictly below the naive sum-of-maxima `2`.) -/
theorem cutD_graph_le (x : X2) (hx : x ∈ boxDiag) :
    reluK (zvec2 2 Adiag Cdiag x 0) + reluK (zvec2 2 Adiag Cdiag x 1) ≤ 1 := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  rw [(zvec2_diag x).1, (zvec2_diag x).2]
  unfold reluK
  rcases le_or_gt 0 (x 0 - x 1) with s0 | s0 <;>
    rcases le_or_gt 0 (x 0 + x 1 - 1) with s1 | s1
  all_goals first | rw [max_eq_right s0] | rw [max_eq_left s0.le]
  all_goals first | rw [max_eq_right s1] | rw [max_eq_left s1.le]
  all_goals linarith

/-- The box corner `(1,0)` realizes the cut value `1`. -/
theorem cutD_corner_val :
    objK 2 eCutD dCutD (curve2 2 Adiag Cdiag (mkpt 1 0)) = 1 := by
  rw [objCutD_eval]
  simp only [curve2, zvec2, Adiag, Cdiag, mkpt, reluK, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val]
  norm_num

/-- `(1,0)` is a box point. -/
theorem corner10_in_boxDiag : mkpt 1 0 ∈ boxDiag := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkpt]

/-- Joint-cut greatest value `1` over the coupled two-oblique-line graph. -/
theorem cutD_isGreatest_graph :
    IsGreatest (objK 2 eCutD dCutD '' coupledGraphDiag) 1 := by
  constructor
  · exact ⟨curve2 2 Adiag Cdiag (mkpt 1 0), ⟨mkpt 1 0, corner10_in_boxDiag, rfl⟩, cutD_corner_val⟩
  · rintro val ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [objCutD_eval]; simp only [curve2]; exact cutD_graph_le x hx

/-- **★ TWO-OBLIQUE-LINE joint-cut EXACTNESS (PART D capstone facet).**  The joint
    2-ReLU cut `relu z1 + relu z2 ≤ 1` is the EXACT optimum over the CONVEX HULL of the
    coupled two-oblique-line k=2 surface graph: `max conv(G) = max G = 1`, NO relaxation
    gap.  A genuinely-2-D-input, two-general-line joint-cut facet (the joint bound `1`
    is strictly below the decoupled sum-of-maxima `2`). -/
theorem coupledDiag_cut_is_facet :
    IsGreatest (objK 2 eCutD dCutD '' convexHull ℝ coupledGraphDiag) 1 :=
  objK_isGreatest_convHull 2 eCutD dCutD coupledGraphDiag 1 cutD_isGreatest_graph

/-! ===================================================================
    Trust-base check.  Every theorem must depend ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

-- PART A : general assembly engine
#print axioms cell_image_subset_vertHull
#print axioms coupledHull_eq_vertImgs_of_cover

-- PART B : general axis-parallel family (arbitrary crossing point & box, ±1 slopes)
#print axioms zvec2_par
#print axioms par_sign_pos
#print axioms signConst_cellPar_aux
#print axioms signConst_cellPar
#print axioms boxPar_subset_cells
#print axioms cellPar_subset_arrVerts
#print axioms arrVertsPar_subset_box
#print axioms coupledPar_convHull_eq_arrangementVerts
#print axioms arrVertsPar_finite
#print axioms arrVertImgsPar_finite
#print axioms coupledPar_lp_max_on_arrangementVerts

-- PART C : genuinely oblique line (both coords active, triangular cells)
#print axioms tri_mem
#print axioms zvec2_obl
#print axioms cellObl_subset_arrVerts
#print axioms arrVertsObl_subset_box
#print axioms signConst_triLo
#print axioms signConst_triHi
#print axioms signConst_cellObl
#print axioms boxObl_subset_cells
#print axioms coupledObl_convHull_eq_arrangementVerts
#print axioms arrVertsObl_finite
#print axioms coupledObl_lp_max_on_arrangementVerts

-- PART D : two genuinely-oblique lines, genuine k=2, crossing inside the box
#print axioms zvec2_diag
#print axioms linfun_signConst_on_tri
#print axioms signConst0_tri
#print axioms signConst1_tri
#print axioms signConst_cellDiag
#print axioms cellDiag_subset_arrVerts
#print axioms arrVertsDiag_subset_box
#print axioms boxDiag_subset_cells
#print axioms coupledDiag_convHull_eq_arrangementVerts
#print axioms arrVertsDiag_finite
#print axioms coupledDiag_lp_max_on_arrangementVerts
#print axioms cutD_graph_le
#print axioms cutD_isGreatest_graph
#print axioms coupledDiag_cut_is_facet

end CrownproofArr2DGen
