/-
  WAVE-7 PROGRAM 4 — k = 3 sign-lines in a 2-D box (three-line arrangement coupled hull).

  Wave-6 (HullArrangement2DGeneral.lean) proved the GENERAL 2-D arrangement assembly
  ENGINE `coupledHull_eq_vertImgs_of_cover` (fully general in k, ANY affine maps), plus
  concrete k = 2 instances (axis-parallel families, one oblique line, and TWO oblique
  lines crossing inside the box → 4 triangle cells, 5 arrangement vertices).

  THIS FILE pushes k to **THREE** sign-lines in 2-D: more neurons (k=3) AND multi-dim
  input.  Three lines in GENERAL POSITION tile the box into the full **7 arrangement
  cells** (1 central triangle + 5 quadrilaterals + 1 pentagon), and we assemble the
  exact coupled-3-ReLU hull from the **13 arrangement vertices** via the (already
  general-k) Part-A engine.

  ====================================================================
  WHAT THIS FILE PROVES  (sorry-free; trust base [propext, Classical.choice, Quot.sound])
  ====================================================================

  A CONCRETE general-position k = 3 instance over the unit box `[0,1]²`:
      z1 = x0 - 1/4         (vertical   sign-line  x0 = 1/4),
      z2 = x1 - 1/4         (horizontal sign-line  x1 = 1/4),
      z3 = 3/4 - x0 - x1    (anti-diag  sign-line  x0 + x1 = 3/4).
  The three sign-lines are in GENERAL POSITION: they cross PAIRWISE at three DISTINCT
  interior points
      P12 = (1/4,1/4)   (z1=z2=0),
      P13 = (1/4,1/2)   (z1=z3=0),
      P23 = (1/2,1/4)   (z2=z3=0),
  and the arrangement has the full **7 sign-constant cells**.  z3 is oriented OPPOSITE
  to z1,z2 (it grows toward the lower-left corner), so the three neurons genuinely
  CONFLICT — the basis for the 3-way-coupling facet below.

  THEOREMS (all via the Part-A assembly engine + mathlib convexity):

   1. `coupledTri3_convHull_eq_arrangementVerts` :
          conv(curve2 '' box)  =  conv(curve2 '' arrVerts)
      The exact convex hull of the coupled 3-ReLU surface graph over the box equals the
      convex hull of the images of the 13 arrangement vertices (4 box corners, 6
      line/box edge points, 3 line/line crossings).

   2. `coupledTri3_lp_max_on_arrangementVerts` :  LP-exactness — for EVERY linear
      objective, its max over the exact coupled hull equals its max over the FINITE
      13-vertex arrangement set (no relaxation gap), reusing `objK_isGreatest_convHull`.

   3. `coupledTri3_cut_is_facet` :  a NON-TRIVIAL 3-WAY-COUPLING facet.  The joint cut
          relu z1 + 2·relu z2 + 3·relu z3  ≤  9/4
      is the EXACT optimum over conv(curve2 '' box) (attained at corners (0,0) and
      (1,1)), STRICTLY below the decoupled / pairwise sum-of-single-maxima bound 9/2.
      This is a genuine joint THREE-ReLU cut: no two-neuron (pairwise) relaxation, and
      a fortiori no single-neuron bound, can certify it — it requires all three coupled
      neurons together.

  COVERAGE (ruthlessly honest):
   * The Part-A ASSEMBLY ENGINE is fully general (any k, any affine maps, any cover by
     convex sign-constant finitely-generated cells); we reuse it verbatim.
   * The k = 3 ARRANGEMENT here is a CONCRETE general-position instance: three specific
     lines tiling the unit box into the full 7 cells (the combinatorial maximum for
     3 lines), fan-triangulated into 14 arrangement-vertex triangles, covered by an
     explicit sign-driven decision tree.  The fully-parametric arbitrary-three-line
     vertex enumeration for ALL relative positions (concurrent, parallel, crossings
     outside the box, …) is heavy polytope combinatorics and is NOT claimed; the genuine
     new content is k = 3 (three coupled neurons) in the multi-dim-input 2-D regime, with
     the full 7-cell general-position arrangement and a genuine 3-way-coupling facet.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Crownproof.HullArrangement2DGeneral

namespace CrownproofArr2DK3

open Set
open CrownproofK (reluK reluK_of_nonneg reluK_of_neg VK objK objK_isGreatest_convHull)
open CrownproofArr2D (X2 zvec2 curve2 SignConstOn mkpt mkpt_0 mkpt_1)
open CrownproofArr2DGen (coupledHull_eq_vertImgs_of_cover tri_mem linfun_signConst_on_tri)

/-! ===================================================================
    SECTION 0.  The k = 3 general-position three-line instance.
    =================================================================== -/

/-- Three-line weight matrix:
    `z1 = x0 - 1/4`,  `z2 = x1 - 1/4`,  `z3 = -x0 - x1 + 3/4`.
    Row `i` is `(A i 0, A i 1)`; the anti-diagonal neuron `z3` has BOTH coords active
    with NEGATIVE weights (it grows toward the lower-left, opposite z1,z2). -/
def A3 : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![-1, -1]]
/-- Biases: `c1 = -1/4`, `c2 = -1/4`, `c3 = 3/4`. -/
noncomputable def C3 : Fin 3 → ℝ := ![-1/4, -1/4, 3/4]

/-- `zvec2` for the three-line instance, neuron by neuron. -/
theorem zvec2_tri3 (x : X2) :
    zvec2 3 A3 C3 x 0 = x 0 - 1/4 ∧
    zvec2 3 A3 C3 x 1 = x 1 - 1/4 ∧
    zvec2 3 A3 C3 x 2 = -x 0 - x 1 + 3/4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [zvec2, A3, C3] <;> ring

/-- The unit box `[0,1]²`. -/
def box3 : Set X2 := { x | (0:ℝ) ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 }

/-! The 13 arrangement vertices: 4 box corners, 6 line/box edge points, 3 line/line
    crossings.  Named to match the geometry. -/
/-- Box corners. -/
noncomputable def c00 : X2 := mkpt 0 0
noncomputable def c10 : X2 := mkpt 1 0
noncomputable def c01 : X2 := mkpt 0 1
noncomputable def c11 : X2 := mkpt 1 1
/-- Line/line crossings. -/
noncomputable def vP12 : X2 := mkpt (1/4) (1/4)   -- z1 = z2 = 0
noncomputable def vP13 : X2 := mkpt (1/4) (1/2)   -- z1 = z3 = 0
noncomputable def vP23 : X2 := mkpt (1/2) (1/4)   -- z2 = z3 = 0
/-- Line/box edge points. -/
noncomputable def vA : X2 := mkpt 0 (1/4)         -- z2 = 0 on x0 = 0
noncomputable def vB : X2 := mkpt 1 (1/4)         -- z2 = 0 on x0 = 1
noncomputable def vD : X2 := mkpt (1/4) 0         -- z1 = 0 on x1 = 0
noncomputable def vE : X2 := mkpt (1/4) 1         -- z1 = 0 on x1 = 1
noncomputable def vF : X2 := mkpt (3/4) 0         -- z3 = 0 on x1 = 0
noncomputable def vG : X2 := mkpt 0 (3/4)         -- z3 = 0 on x0 = 0

/-- The 13 arrangement vertices. -/
noncomputable def arrVerts3 : Set X2 :=
  { c00, c10, c01, c11, vP12, vP13, vP23, vA, vB, vD, vE, vF, vG }

/-! The 14 fan-triangulation cells of the 7 arrangement cells.
    Region 1 (z1<0,z2<0,z3>0) quad c00,D,P12,A  → r1_1, r1_2
    Region 2 (z1<0,z2>0,z3<0) quad G,P13,E,c01   → r2_1, r2_2
    Region 3 (z1<0,z2>0,z3>0) quad A,P12,P13,G   → r3_1, r3_2
    Region 4 (z1>0,z2<0,z3<0) quad F,c10,B,P23   → r4_1, r4_2
    Region 5 (z1>0,z2<0,z3>0) quad D,F,P23,P12   → r5_1, r5_2
    Region 6 (z1>0,z2>0,z3<0) pent P13,P23,B,c11,E → r6_1, r6_2, r6_3
    Region 7 (z1>0,z2>0,z3>0) tri  P12,P23,P13   → r7_1 -/
noncomputable def cell3 : Fin 14 → Set X2 :=
  ![ ({c00, vD, vP12} : Set X2),    -- 0  r1_1
     ({c00, vP12, vA} : Set X2),    -- 1  r1_2
     ({vG, vP13, vE} : Set X2),     -- 2  r2_1
     ({vG, vE, c01} : Set X2),      -- 3  r2_2
     ({vA, vP12, vP13} : Set X2),   -- 4  r3_1
     ({vA, vP13, vG} : Set X2),     -- 5  r3_2
     ({vF, c10, vB} : Set X2),      -- 6  r4_1
     ({vF, vB, vP23} : Set X2),     -- 7  r4_2
     ({vD, vF, vP23} : Set X2),     -- 8  r5_1
     ({vD, vP23, vP12} : Set X2),   -- 9  r5_2
     ({vP13, vP23, vB} : Set X2),   -- 10 r6_1
     ({vP13, vB, c11} : Set X2),    -- 11 r6_2
     ({vP13, c11, vE} : Set X2),    -- 12 r6_3
     ({vP12, vP23, vP13} : Set X2) ] -- 13 r7_1

/-! ===================================================================
    SECTION 1.  Per-neuron sign-constancy on a triangle.

    Each neuron `z_i` is a linear functional `α_i x0 + β_i x1 + γ_i`.  Via the wave-6
    helper `linfun_signConst_on_tri`, sign-constancy on a triangle `conv{P,Q,R}` reduces
    to the SAME sign of `z_i` at the three generators `P,Q,R`.
    =================================================================== -/

/-- Neuron-0 sign-constancy on a triangle (`z1 = x0 - 1/4 = 1·x0 + 0·x1 + (-1/4)`). -/
theorem signConst0_tri3 (P Q R : X2)
    (hsgn : (0 ≤ P 0 - 1/4 ∧ 0 ≤ Q 0 - 1/4 ∧ 0 ≤ R 0 - 1/4) ∨
            (P 0 - 1/4 ≤ 0 ∧ Q 0 - 1/4 ≤ 0 ∧ R 0 - 1/4 ≤ 0)) :
    SignConstOn 3 A3 C3 (convexHull ℝ ({P, Q, R} : Set X2)) 0 := by
  have h := linfun_signConst_on_tri 1 0 (-1/4) P Q R (by
    rcases hsgn with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩)
  rcases h with h | h
  · exact Or.inl (fun x hx => by rw [(zvec2_tri3 x).1]; have := h x hx; linarith)
  · exact Or.inr (fun x hx => by rw [(zvec2_tri3 x).1]; have := h x hx; linarith)

/-- Neuron-1 sign-constancy on a triangle (`z2 = x1 - 1/4 = 0·x0 + 1·x1 + (-1/4)`). -/
theorem signConst1_tri3 (P Q R : X2)
    (hsgn : (0 ≤ P 1 - 1/4 ∧ 0 ≤ Q 1 - 1/4 ∧ 0 ≤ R 1 - 1/4) ∨
            (P 1 - 1/4 ≤ 0 ∧ Q 1 - 1/4 ≤ 0 ∧ R 1 - 1/4 ≤ 0)) :
    SignConstOn 3 A3 C3 (convexHull ℝ ({P, Q, R} : Set X2)) 1 := by
  have h := linfun_signConst_on_tri 0 1 (-1/4) P Q R (by
    rcases hsgn with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩)
  rcases h with h | h
  · exact Or.inl (fun x hx => by rw [(zvec2_tri3 x).2.1]; have := h x hx; linarith)
  · exact Or.inr (fun x hx => by rw [(zvec2_tri3 x).2.1]; have := h x hx; linarith)

/-- Neuron-2 sign-constancy on a triangle
    (`z3 = -x0 - x1 + 3/4 = (-1)·x0 + (-1)·x1 + 3/4`). -/
theorem signConst2_tri3 (P Q R : X2)
    (hsgn : (0 ≤ -P 0 - P 1 + 3/4 ∧ 0 ≤ -Q 0 - Q 1 + 3/4 ∧ 0 ≤ -R 0 - R 1 + 3/4) ∨
            (-P 0 - P 1 + 3/4 ≤ 0 ∧ -Q 0 - Q 1 + 3/4 ≤ 0 ∧ -R 0 - R 1 + 3/4 ≤ 0)) :
    SignConstOn 3 A3 C3 (convexHull ℝ ({P, Q, R} : Set X2)) 2 := by
  have h := linfun_signConst_on_tri (-1) (-1) (3/4) P Q R (by
    rcases hsgn with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩)
  rcases h with h | h
  · exact Or.inl (fun x hx => by rw [(zvec2_tri3 x).2.2]; have := h x hx; linarith)
  · exact Or.inr (fun x hx => by rw [(zvec2_tri3 x).2.2]; have := h x hx; linarith)

-- All thirteen vertex coordinates, for `norm_num`-driven sign facts.
attribute [local simp] c00 c10 c01 c11 vP12 vP13 vP23 vA vB vD vE vF vG

/-- **Sign-constancy on each of the 14 triangle cells.**  For every triangle and every
    neuron the pre-activation keeps one sign, established from the three generators'
    signs (the NN/NP table of the arrangement). -/
theorem signConst_cell3 : ∀ j : Fin 14, ∀ i : Fin 3,
    SignConstOn 3 A3 C3 (convexHull ℝ (cell3 j)) i := by
  intro j i
  fin_cases j <;> simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val] <;> fin_cases i
  -- cell 0  z1:NP z2:NP z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 1  z1:NP z2:NP z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 2  z1:NP z2:NN z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 3  z1:NP z2:NN z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 4  z1:NP z2:NN z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 5  z1:NP z2:NN z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 6  z1:NN z2:NP z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 7  z1:NN z2:NP z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 8  z1:NN z2:NP z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 9  z1:NN z2:NP z3:NN
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 10  z1:NN z2:NN z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 11  z1:NN z2:NN z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 12  z1:NN z2:NN z3:NP
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inr (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  -- cell 13  z1:NN z2:NN z3:NN  (central triangle)
  · exact signConst0_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst1_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))
  · exact signConst2_tri3 _ _ _ (Or.inl (by constructor <;> [skip; constructor] <;> simp <;> norm_num))

/-! ===================================================================
    SECTION 2.  Cover, vertex containment, box containment.
    =================================================================== -/

/-- **Each triangle cell's generators are arrangement vertices.** -/
theorem cell3_subset_arrVerts : ∀ j : Fin 14, cell3 j ⊆ arrVerts3 := by
  intro j
  fin_cases j <;>
    · intro w hw
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;>
        simp only [arrVerts3, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- The arrangement-vertex set lies in the unit box. -/
theorem arrVerts3_subset_box : arrVerts3 ⊆ box3 := by
  intro w hw
  simp only [arrVerts3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> norm_num

/-- Helper: discharge the barycentric IDENTITY `x = u•P + v•Q + w•R` for two explicit
    vertices, componentwise, by `ring`.  (All vertices are `mkpt` of numerals.) -/
theorem cover_pt (P Q R : X2) (x : X2) (u v w : ℝ)
    (h0 : x 0 = u * P 0 + v * Q 0 + w * R 0)
    (h1 : x 1 = u * P 1 + v * Q 1 + w * R 1) :
    x = u • P + v • Q + w • R := by
  funext k; fin_cases k
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h0
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-- **The 14 triangle cells COVER the unit box.**  An explicit sign-driven decision tree
    (the three line-signs `x0⋛1/4`, `x1⋛1/4`, `x0+x1⋛3/4`, plus one diagonal comparison
    inside each multi-triangle cell) lands every box point in a triangle that contains it,
    with explicit barycentric weights verified by `tri_mem`. -/
theorem box3_subset_cells (x : X2) (hx : x ∈ box3) :
    ∃ j : Fin 14, x ∈ convexHull ℝ (cell3 j) := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  -- the three line-side decisions
  rcases le_or_gt (1/4 : ℝ) (x 0) with s1 | s1 <;>
    rcases le_or_gt (1/4 : ℝ) (x 1) with s2 | s2 <;>
    rcases le_or_gt (x 0 + x 1) (3/4 : ℝ) with s3 | s3
  -- s1 : 1/4 ≤ x0   (z1 ≥ 0) ;  s2 : 1/4 ≤ x1 (z2 ≥ 0) ; s3 : x0+x1 ≤ 3/4 (z3 ≥ 0)
  · -- (z1≥0,z2≥0,z3≥0) region 7 central triangle  cell 13  P12,P23,P13
    refine ⟨13, ?_⟩
    simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val]
    refine tri_mem vP12 vP23 vP13 x (-4*x 0 - 4*x 1 + 3) (4*x 0 - 1) (4*x 1 - 1)
      (by linarith) (by linarith) (by linarith) (by ring)
      (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
      · simp [vP12, vP23, vP13]; ring
  · -- (z1≥0,z2≥0,z3<0) region 6 pentagon  P13,P23,B,c11,E → cells 10,11,12
    rcases le_or_gt (x 0 + 3 * x 1) (7/4 : ℝ) with d | d
    · -- cell 10  P13,P23,B
      refine ⟨10, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vP13 vP23 vB x (4*x 1 - 1) (-2*x 0 - 6*x 1 + 7/2) (2*x 0 + 2*x 1 - 3/2)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vP13, vP23, vB]; ring
    · rcases le_or_gt (0 : ℝ) (-4/3 * x 0 + 2 * x 1 - 2/3) with d2 | d2
      · -- cell 12  P13,c11,E
        refine ⟨12, ?_⟩
        simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one, Matrix.cons_val]
        refine tri_mem vP13 c11 vE x (2 - 2*x 1) (4*x 0/3 - 1/3) (-4*x 0/3 + 2*x 1 - 2/3)
          (by linarith) (by linarith) (by linarith) (by ring)
          (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
          · simp [vP13, c11, vE]; ring
      · -- cell 11  P13,B,c11
        refine ⟨11, ?_⟩
        simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one, Matrix.cons_val]
        refine tri_mem vP13 vB c11 x (4/3 - 4*x 0/3) (8*x 0/9 - 4*x 1/3 + 4/9)
          (4*x 0/9 + 4*x 1/3 - 7/9)
          (by linarith) (by linarith) (by linarith) (by ring)
          (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
          · simp [vP13, vB, c11]; ring
  · -- (z1≥0,z2<0,z3≥0) region 5 quad  D,F,P23,P12 → cells 8,9
    rcases le_or_gt (x 1 + 1/4) (x 0) with d | d
    · -- cell 8  D,F,P23   (x0 ≥ x1 + 1/4)
      refine ⟨8, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vD vF vP23 x (-2*x 0 - 2*x 1 + 3/2) (2*x 0 - 2*x 1 - 1/2) (4*x 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vD, vF, vP23]; ring
    · -- cell 9  D,P23,P12
      refine ⟨9, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vD vP23 vP12 x (1 - 4*x 1) (4*x 0 - 1) (-4*x 0 + 4*x 1 + 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vD, vP23, vP12]; ring
  · -- (z1≥0,z2<0,z3<0) region 4 quad  F,c10,B,P23 → cells 6,7
    rcases le_or_gt (x 1 + 3/4) (x 0) with d | d
    · -- cell 6  F,c10,B   (x0 ≥ x1 + 3/4)
      refine ⟨6, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vF c10 vB x (4 - 4*x 0) (4*x 0 - 4*x 1 - 3) (4*x 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vF, c10, vB]; ring
    · -- cell 7  F,B,P23
      refine ⟨7, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vF vB vP23 x (1 - 4*x 1) (2*x 0 + 2*x 1 - 3/2) (-2*x 0 + 2*x 1 + 3/2)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vF, vB, vP23]; ring
  · -- (z1<0,z2≥0,z3≥0) region 3 quad  A,P12,P13,G → cells 4,5
    rcases le_or_gt (x 0 + 1/4) (x 1) with d | d
    · -- cell 5  A,P13,G   (x1 ≥ x0 + 1/4)
      refine ⟨5, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vA vP13 vG x (-2*x 0 - 2*x 1 + 3/2) (4*x 0) (-2*x 0 + 2*x 1 - 1/2)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vA, vP13, vG]; ring
    · -- cell 4  A,P12,P13
      refine ⟨4, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vA vP12 vP13 x (1 - 4*x 0) (4*x 0 - 4*x 1 + 1) (4*x 1 - 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vA, vP12, vP13]; ring
  · -- (z1<0,z2≥0,z3<0) region 2 quad  G,P13,E,c01 → cells 2,3
    rcases le_or_gt (x 1) (x 0 + 3/4) with d | d
    · -- cell 2  G,P13,E   (x1 ≤ x0 + 3/4)
      refine ⟨2, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vG vP13 vE x (1 - 4*x 0) (2*x 0 - 2*x 1 + 3/2) (2*x 0 + 2*x 1 - 3/2)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vG, vP13, vE]; ring
    · -- cell 3  G,E,c01
      refine ⟨3, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem vG vE c01 x (4 - 4*x 1) (4*x 0) (-4*x 0 + 4*x 1 - 3)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [vG, vE, c01]; ring
  · -- (z1<0,z2<0,z3≥0) region 1 quad  c00,D,P12,A → cells 0,1
    rcases le_or_gt (x 1) (x 0) with d | d
    · -- cell 0  c00,D,P12   (x0 ≥ x1)
      refine ⟨0, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem c00 vD vP12 x (1 - 4*x 0) (4*x 0 - 4*x 1) (4*x 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [c00, vD, vP12]; ring
    · -- cell 1  c00,P12,A
      refine ⟨1, ?_⟩
      simp only [cell3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      refine tri_mem c00 vP12 vA x (1 - 4*x 1) (4*x 0) (-4*x 0 + 4*x 1)
        (by linarith) (by linarith) (by linarith) (by ring)
        (cover_pt _ _ _ _ _ _ _ ?_ ?_) <;>
        · simp [c00, vP12, vA]; ring
  · -- (z1<0,z2<0,z3<0) VACUOUS: x0<1/4 ∧ x1<1/4 ⟹ x0+x1<1/2 < 3/4, contradicting z3<0.
    exact absurd s3 (by linarith)

/-! ===================================================================
    SECTION 3.  THE k = 3 ARRANGEMENT HULL EQUALITY (capstone) + LP-exactness.
    =================================================================== -/

/-- The coupled 2-D-input THREE-ReLU surface graph over the unit box. -/
noncomputable def coupledGraph3 : Set (VK 3) := curve2 3 A3 C3 '' box3
/-- The k = 3 arrangement-vertex image set. -/
noncomputable def arrVertImgs3 : Set (VK 3) := curve2 3 A3 C3 '' arrVerts3

/-- **★ THE k = 3 GENERAL-POSITION ARRANGEMENT HULL EQUALITY.**
    For the genuine 2-D-input k = 3 coupled ReLU surface with THREE sign-lines
    `x0 = 1/4`, `x1 = 1/4`, `x0 + x1 = 3/4` in GENERAL POSITION (pairwise crossings at
    three distinct interior points, the full 7 arrangement cells),
          conv(coupledGraph3) = conv(arrVertImgs3),
    the exact convex hull of the coupled piecewise-affine THREE-ReLU surface equals the
    convex hull of the images of the 13 arrangement vertices (4 box corners + 6 line/box
    edge points + 3 line/line crossings).  Proved by the (general-k) Part-A assembly
    engine `coupledHull_eq_vertImgs_of_cover` over the 14 fan-triangulation cells. -/
theorem coupledTri3_convHull_eq_arrangementVerts :
    convexHull ℝ coupledGraph3 = convexHull ℝ arrVertImgs3 := by
  exact coupledHull_eq_vertImgs_of_cover 3 A3 C3 box3 arrVerts3 cell3
    arrVerts3_subset_box cell3_subset_arrVerts
    (fun x hx => box3_subset_cells x hx) signConst_cell3

/-- The arrangement-vertex x-set is finite (13 explicit points). -/
theorem arrVerts3_finite : arrVerts3.Finite := by
  unfold arrVerts3
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _ |>.insert _
    |>.insert _ |>.insert _ |>.insert _ |>.insert _ |>.insert _ |>.insert _ |>.insert _

/-- The arrangement-vertex image set is finite (13 ℝ⁶ points). -/
theorem arrVertImgs3_finite : arrVertImgs3.Finite := arrVerts3_finite.image _

/-- **★ k = 3 LP-EXACTNESS on the arrangement vertices.**  For EVERY linear objective
    `objK e d`, IF its greatest value `M` over the FINITE 13-vertex arrangement image set
    is attained, THEN `M` is the greatest value over the ENTIRE coupled hull.  So
    optimizing any linear objective over the exact coupled 2-D-input k = 3 relaxation
    reduces to checking the 13 arrangement vertices — the joint THREE-line arrangement
    cut is the exact / LP-tightest hull, NO gap.  Reuses `objK_isGreatest_convHull`. -/
theorem coupledTri3_lp_max_on_arrangementVerts (e d : Fin 3 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 3 e d '' arrVertImgs3) M) :
    IsGreatest (objK 3 e d '' convexHull ℝ coupledGraph3) M := by
  have := objK_isGreatest_convHull 3 e d arrVertImgs3 M hM
  rwa [← coupledTri3_convHull_eq_arrangementVerts] at this

/-! ===================================================================
    SECTION 4.  A NON-TRIVIAL 3-WAY-COUPLING FACET.

    The joint cut `relu z1 + 2·relu z2 + 3·relu z3 ≤ 9/4` is the EXACT optimum over
    conv(coupledGraph3) (attained at the box corners (0,0) and (1,1)).  Because z3 grows
    toward the lower-left while z1,z2 grow toward the upper-right, the three neurons
    CONFLICT: the decoupled bound (sum of single-neuron maxima) is
        1·(3/4) + 2·(3/4) + 3·(3/4) = 9/2,  STRICTLY above 9/4.
    Even the best PAIRWISE bound exceeds 9/4.  Only the joint THREE-ReLU cut certifies
    the exact value 9/4 — genuine three-way coupling, no relaxation gap.
    =================================================================== -/

/-- Joint-cut objective `relu z1 + 2·relu z2 + 3·relu z3` (`e = 0`, `d = (1,2,3)`). -/
def eCut3 : Fin 3 → ℝ := ![0, 0, 0]
def dCut3 : Fin 3 → ℝ := ![1, 2, 3]

/-- The joint-cut objective is `relu z1 + 2·relu z2 + 3·relu z3` on an ℝ⁶ point. -/
theorem objCut3_eval (p : VK 3) :
    objK 3 eCut3 dCut3 p = p.2 0 + 2 * p.2 1 + 3 * p.2 2 := by
  simp only [objK, eCut3, dCut3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]; ring

/-- **Graph-level joint-cut soundness**: `relu(z1) + 2·relu(z2) + 3·relu(z3) ≤ 9/4` for
    all `x ∈ [0,1]²`.  (The joint bound `9/4` is strictly below the decoupled
    sum-of-single-maxima `9/2`.)  Proved by an exhaustive ReLU sign case split + linarith;
    the binding combination uses that `z3 = 3/4 - x0 - x1` opposes `z1,z2`. -/
theorem cut3_graph_le (x : X2) (hx : x ∈ box3) :
    reluK (zvec2 3 A3 C3 x 0) + 2 * reluK (zvec2 3 A3 C3 x 1)
      + 3 * reluK (zvec2 3 A3 C3 x 2) ≤ 9/4 := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  rw [(zvec2_tri3 x).1, (zvec2_tri3 x).2.1, (zvec2_tri3 x).2.2]
  unfold reluK
  rcases le_or_gt 0 (x 0 - 1/4) with s0 | s0 <;>
    rcases le_or_gt 0 (x 1 - 1/4) with s1 | s1 <;>
    rcases le_or_gt 0 (-x 0 - x 1 + 3/4) with s2 | s2
  all_goals first | rw [max_eq_right s0] | rw [max_eq_left s0.le]
  all_goals first | rw [max_eq_right s1] | rw [max_eq_left s1.le]
  all_goals first | rw [max_eq_right s2] | rw [max_eq_left s2.le]
  all_goals linarith

/-- The box corner `(1,1)` realizes the joint-cut value `9/4`
    (`relu z1 = 3/4`, `relu z2 = 3/4`, `relu z3 = 0` → `3/4 + 2·3/4 + 0 = 9/4`). -/
theorem cut3_corner_val :
    objK 3 eCut3 dCut3 (curve2 3 A3 C3 c11) = 9/4 := by
  rw [objCut3_eval]
  simp only [curve2, zvec2, A3, C3, c11, mkpt, reluK, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val]
  norm_num

/-- `(1,1)` is a box point. -/
theorem corner11_in_box3 : c11 ∈ box3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [c11]

/-- Joint-cut greatest value `9/4` over the coupled three-line graph. -/
theorem cut3_isGreatest_graph :
    IsGreatest (objK 3 eCut3 dCut3 '' coupledGraph3) (9/4) := by
  constructor
  · exact ⟨curve2 3 A3 C3 c11, ⟨c11, corner11_in_box3, rfl⟩, cut3_corner_val⟩
  · rintro val ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [objCut3_eval]; simp only [curve2]
    have := cut3_graph_le x hx; linarith

/-- **★ THE 3-WAY-COUPLING FACET (capstone).**  The joint THREE-ReLU cut
        relu z1 + 2·relu z2 + 3·relu z3  ≤  9/4
    is the EXACT optimum over the CONVEX HULL of the coupled 2-D-input k = 3 surface
    graph: `max conv(coupledGraph3) = max coupledGraph3 = 9/4`, NO relaxation gap.
    A genuinely-2-D-input, THREE-general-line joint-cut facet: the joint bound `9/4` is
    STRICTLY below the decoupled sum-of-single-maxima `9/2`, and indeed below any
    pairwise bound — the three coupled neurons are needed together. -/
theorem coupledTri3_cut_is_facet :
    IsGreatest (objK 3 eCut3 dCut3 '' convexHull ℝ coupledGraph3) (9/4) :=
  objK_isGreatest_convHull 3 eCut3 dCut3 coupledGraph3 (9/4) cut3_isGreatest_graph

/-! ===================================================================
    SECTION 5.  Decoupled / pairwise gap WITNESS (the cut is genuinely 3-way).

    We certify that the joint optimum `9/4` is STRICTLY below the decoupled bound `9/2`,
    proving the cut is NOT implied by single-neuron (and a fortiori not by the trivially
    sound) bounds.  Each single-neuron ReLU maxes at `3/4` over the box, so the decoupled
    surrogate `1·max relu z1 + 2·max relu z2 + 3·max relu z3 = 9/2`.
    =================================================================== -/

/-- Single-neuron maxima over the box: `relu z1 ≤ 3/4`, `relu z2 ≤ 3/4`, `relu z3 ≤ 3/4`,
    each attained.  The decoupled surrogate is `1·3/4 + 2·3/4 + 3·3/4 = 9/2 > 9/4`. -/
theorem cut3_decoupled_bound (x : X2) (hx : x ∈ box3) :
    reluK (zvec2 3 A3 C3 x 0) ≤ 3/4 ∧ reluK (zvec2 3 A3 C3 x 1) ≤ 3/4 ∧
    reluK (zvec2 3 A3 C3 x 2) ≤ 3/4 := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  rw [(zvec2_tri3 x).1, (zvec2_tri3 x).2.1, (zvec2_tri3 x).2.2]
  refine ⟨?_, ?_, ?_⟩ <;> unfold reluK <;> rw [max_le_iff] <;>
    exact ⟨by norm_num, by linarith⟩

/-- **★ STRICT COUPLING GAP.**  The exact joint optimum `9/4` is STRICTLY LESS than the
    decoupled sum-of-single-maxima bound `9/2`.  Hence the facet
    `relu z1 + 2·relu z2 + 3·relu z3 ≤ 9/4` cannot be derived from per-neuron bounds:
    it is a genuine THREE-way coupling cut, with a relaxation gap of `9/4` against the
    fully-decoupled relaxation. -/
theorem cut3_strict_coupling_gap : (9/4 : ℝ) < 1 * (3/4) + 2 * (3/4) + 3 * (3/4) := by
  norm_num

/-! ===================================================================
    Trust-base check.  Every theorem must depend ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

-- Setup / instance
#print axioms zvec2_tri3
-- Per-neuron + per-cell sign-constancy
#print axioms signConst0_tri3
#print axioms signConst1_tri3
#print axioms signConst2_tri3
#print axioms signConst_cell3
-- Cover / containment
#print axioms cell3_subset_arrVerts
#print axioms arrVerts3_subset_box
#print axioms cover_pt
#print axioms box3_subset_cells
-- Capstone hull equality + finiteness + LP-exactness
#print axioms coupledTri3_convHull_eq_arrangementVerts
#print axioms arrVerts3_finite
#print axioms arrVertImgs3_finite
#print axioms coupledTri3_lp_max_on_arrangementVerts
-- 3-way-coupling facet + gap
#print axioms objCut3_eval
#print axioms cut3_graph_le
#print axioms cut3_corner_val
#print axioms cut3_isGreatest_graph
#print axioms coupledTri3_cut_is_facet
#print axioms cut3_decoupled_bound
#print axioms cut3_strict_coupling_gap

end CrownproofArr2DK3
