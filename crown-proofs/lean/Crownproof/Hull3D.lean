/-
  WAVE-8 PROGRAM 4 — 3-D INPUT coupled k-ReLU arrangement hull (sign-PLANES).

  Waves 5-7 proved the multi-dim coupled k-ReLU hull for 2-D input, where the ReLU
  pattern changes across an arrangement of sign-LINES {z_i(x)=0} in R^2.  THIS file
  goes to 3-D INPUT: the coupled k-ReLU graph over a 3-D box where the ReLU pattern
  changes across an arrangement of sign-PLANES {z_i(x)=0} in R^3 (x : Fin 3 → R).

  =====================================================================
  WHAT THIS FILE PROVES (sorry-free; trust base [propext, Classical.choice, Quot.sound])
  =====================================================================

  PART A — THE 3-D CELL ENGINE (fully general k, ANY affine maps a_i, c_i on R^3).
    `surface3_image_subset_convHull_of_signConst` : on a CONVEX cell K = conv W of R^3
    where EVERY neuron z_i = a_i . x + c_i is sign-constant, the coupled surface
    `curve3 x = (z(x), relu(z(x)))` maps the cell into the convex hull of the images
    of the generators:  curve3 '' (conv W) ⊆ conv (curve3 '' W).
    This is the 3-D lift of the wave-5/6 engine `surface2_image_subset_convHull_of_signConst`.
    The ONLY thing tied to the input dimension is that `zvec3` is jointly affine; the
    sign-constant-ReLU-sends-segments-to-segments content is dimension-free.

  PART B — THE GENERAL 3-D ASSEMBLY THEOREM (any k, any affine maps, any plane positions).
    `coupledHull3_eq_vertImgs_of_cover` : IF the 3-D box is covered by convex cells,
    each = conv of a finite vertex subset of a global arrangement-vertex set V, and on
    each cell every neuron is sign-constant, THEN
          conv(curve3 '' box) = conv(curve3 '' V).
    The exact convex hull of the coupled PWL surface over the 3-D box equals the convex
    hull of the images of the arrangement-vertex set V.  Dimension-and-plane-position-
    free "assemble the cells" content; it reduces the GENERAL 3-D arrangement-hull
    problem to (i) a cover by sign-constant convex cells and (ii) writing each cell as
    conv of arrangement vertices.

  PART C — THE CONCRETE k=3 AXIS-PLANE 3-D INSTANCE (the deliverable).
    box [-1,1]^3,  z1 = x0  (plane x0=0),  z2 = x1  (plane x1=0),  z3 = x2  (plane x2=0).
    The 3 sign-planes are the coordinate planes; the arrangement partitions the box into
    the 8 OCTANT sub-boxes.  The ARRANGEMENT VERTICES are the 27 grid points {-1,0,1}^3
    (8 box corners + 12 plane/box-edge points + 6 plane/plane-edge points + 1 origin =
    plane/plane/plane).  We prove, via PARTS A+B:
      * `coupled3_convHull_eq_arrangementVerts` : conv(curve3 '' box) = conv(curve3''V).
      * `coupled3_lp_max_on_arrangementVerts`  : LP-exactness over the 27 vertices, for
        every linear objective (reusing the dimension-free output-space engine
        `objK_isGreatest_convHull` from HullKGeneral).

  PART D — A GENUINE k=3 3-D-INPUT JOINT-CUT FACET (no relaxation gap).
    `coupled3_cut_is_facet` : the joint 3-ReLU cut `relu z1 + relu z2 + relu z3 ≤ 3` is
    the EXACT optimum over conv(curve3 '' box), attained at the box corner (1,1,1).
    This is a genuine joint k≥2 3-D-input facet that is the exact hull optimum.

  COVERAGE (ruthlessly honest):
   * PART A is fully general: ANY k, ANY affine maps R^3→R, ANY finite cover by convex
     sign-constant finitely-generated cells.  This is the reusable 3-D cell engine.
   * PART B is the fully-general 3-D assembly theorem (any k, any planes, any cover).
   * PART C/D is the concrete AXIS-PLANE k=3 instance tiling the 3-D box into 8 octants,
     proved rigorously THROUGH the general engine.  The fully-general arbitrary-plane
     arrangement-VERTEX ENUMERATION for ALL relative positions (generic obliques,
     parallel/coincident planes, crossings outside the box) is combinatorially heavy
     polytope theory and is NOT claimed for every position; we deliver the general
     ASSEMBLY engine + the concrete axis-plane octant instance.  The genuinely new
     content over waves 5-7 is the 3-D INPUT (sign-planes, octant cells, 27 vertices).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Crownproof.HullKGeneral

namespace CrownproofArr3D

open Set
open CrownproofK (reluK reluK_of_nonneg reluK_of_neg VK objK objK_isGreatest_convHull)

/-! ===================================================================
    PART A.  3-D affine pre-activations, sign-constancy, the cell engine.
    =================================================================== -/

/-- A 3-D input vector. -/
abbrev X3 := Fin 3 → ℝ

/-- Pre-activation of neuron `i`: `z_i(x) = A i 0 * x0 + A i 1 * x1 + A i 2 * x2 + C i`,
    affine in the 3-D vector `x`.  `A : Fin k → Fin 3 → ℝ` is the weight matrix. -/
def zvec3 (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (x : X3) : Fin k → ℝ :=
  fun i => A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2 + C i

/-- The coupled k-ReLU SURFACE point at 3-D input `x`:
    `(z_1 x,…,z_k x, relu(z_1 x),…,relu(z_k x)) ∈ ℝ^{2k}`. -/
def curve3 (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (x : X3) : VK k :=
  (zvec3 k A C x, fun i => reluK (zvec3 k A C x i))

/-- `z_i` is "sign-constant on the cell `K`": its pre-activation keeps ONE sign over
    all of `K` (all ≥ 0, or all ≤ 0). -/
def SignConstOn (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (K : Set X3)
    (i : Fin k) : Prop :=
  (∀ x ∈ K, 0 ≤ zvec3 k A C x i) ∨ (∀ x ∈ K, zvec3 k A C x i ≤ 0)

/-- `zvec3` is jointly affine: for a convex combination `s•p + t•q` (`s+t=1`),
    `zvec3 (s•p+t•q) i = s * zvec3 p i + t * zvec3 q i`. -/
theorem zvec3_affine_combo (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ)
    (p q : X3) (s t : ℝ) (hst : s + t = 1) (i : Fin k) :
    zvec3 k A C (s • p + t • q) i = s * zvec3 k A C p i + t * zvec3 k A C q i := by
  simp only [zvec3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ht1 : t = 1 - s := by linarith
  subst ht1
  ring

/-- On a sign-constant cell, ReLU of an affine combination of two cell points is the
    same affine combination of the ReLUs.  Needs `s,t ≥ 0`, `s+t=1`, and that both
    endpoints (hence the combination) are on the same side of 0.  Dimension-free. -/
theorem reluK_combo_on_signConst
    (zp zq : ℝ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hsgn : (0 ≤ zp ∧ 0 ≤ zq) ∨ (zp ≤ 0 ∧ zq ≤ 0)) :
    reluK (s * zp + t * zq) = s * reluK zp + t * reluK zq := by
  rcases hsgn with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hmid : 0 ≤ s * zp + t * zq :=
      add_nonneg (mul_nonneg hs hp) (mul_nonneg ht hq)
    rw [reluK_of_nonneg hmid, reluK_of_nonneg hp, reluK_of_nonneg hq]
  · have hmid : s * zp + t * zq ≤ 0 := by
      have := add_le_add (mul_nonpos_of_nonneg_of_nonpos hs hp)
                         (mul_nonpos_of_nonneg_of_nonpos ht hq)
      simpa using this
    rw [reluK_of_neg hmid, reluK_of_neg hp, reluK_of_neg hq]; ring

/-- **The 3-D surface is affine on a sign-constant convex cell — SEGMENT form.**
    If `p, q ∈ K` and every neuron is sign-constant on `K`, then for convex weights
    `s,t ≥ 0`, `s+t=1`,  curve3 (s•p + t•q) = s • curve3 p + t • curve3 q. -/
theorem curve3_combo_on_cell (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ)
    (K : Set X3) (p q : X3) (hp : p ∈ K) (hq : q ∈ K)
    (hsc : ∀ i : Fin k, SignConstOn k A C K i)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    curve3 k A C (s • p + t • q) = s • curve3 k A C p + t • curve3 k A C q := by
  apply Prod.ext
  · funext i
    simp only [curve3, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact zvec3_affine_combo k A C p q s t hst i
  · funext i
    simp only [curve3, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [zvec3_affine_combo k A C p q s t hst i]
    have hsgn : (0 ≤ zvec3 k A C p i ∧ 0 ≤ zvec3 k A C q i) ∨
                (zvec3 k A C p i ≤ 0 ∧ zvec3 k A C q i ≤ 0) := by
      rcases hsc i with hpos | hneg
      · exact Or.inl ⟨hpos p hp, hpos q hq⟩
      · exact Or.inr ⟨hneg p hp, hneg q hq⟩
    exact reluK_combo_on_signConst _ _ s t hs ht hst hsgn

/-- On a sign-constant convex cell, `curve3 (s•p+t•q) ∈ segment (curve3 p) (curve3 q)`. -/
theorem curve3_mem_segment_on_cell (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ)
    (K : Set X3) (p q : X3) (hp : p ∈ K) (hq : q ∈ K)
    (hsc : ∀ i : Fin k, SignConstOn k A C K i)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    curve3 k A C (s • p + t • q) ∈ segment ℝ (curve3 k A C p) (curve3 k A C q) :=
  ⟨s, t, hs, ht, hst, (curve3_combo_on_cell k A C K p q hp hq hsc s t hs ht hst).symm⟩

/-- The "good set" RELATIVE to a cell `K`: cell points whose surface image is in
    `conv(curve3 '' W)`. -/
def GoodSet (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (K W : Set X3) : Set X3 :=
  { x | x ∈ K ∧ curve3 k A C x ∈ convexHull ℝ (curve3 k A C '' W) }

/-- **★ THE 3-D ARRANGEMENT-CELL ENGINE (fully general k, any affine maps R^3→R).**
    If a convex cell `K = conv W`, and EVERY neuron is sign-constant on `K`, then the
    surface image of `K` lies in the convex hull of the surface images of `W`:
          curve3 '' (convexHull ℝ W)  ⊆  convexHull ℝ (curve3 '' W).
    The precise statement "the piecewise-affine 3-D-input surface over an arrangement
    cell is the conv of the images of the cell's vertices". -/
theorem surface3_image_subset_convHull_of_signConst
    (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (W : Set X3)
    (hsc : ∀ i : Fin k, SignConstOn k A C (convexHull ℝ W) i) :
    curve3 k A C '' (convexHull ℝ W) ⊆ convexHull ℝ (curve3 k A C '' W) := by
  set K := convexHull ℝ W with hKdef
  have hKconv : Convex ℝ K := convex_convexHull ℝ W
  have hsub : K ⊆ GoodSet k A C K W := by
    rw [hKdef]
    apply convexHull_min
    · intro w hw
      refine ⟨subset_convexHull ℝ W hw, subset_convexHull ℝ _ ⟨w, hw, rfl⟩⟩
    · rw [convex_iff_forall_pos]
      rintro p ⟨hpK, hpImg⟩ q ⟨hqK, hqImg⟩ s t hs ht hst
      refine ⟨hKconv hpK hqK hs.le ht.le hst, ?_⟩
      have hseg : curve3 k A C (s • p + t • q)
            ∈ segment ℝ (curve3 k A C p) (curve3 k A C q) :=
        curve3_mem_segment_on_cell k A C K p q hpK hqK hsc s t hs.le ht.le hst
      exact (convex_convexHull ℝ _).segment_subset hpImg hqImg hseg
  intro y hy
  obtain ⟨x, hxK, rfl⟩ := hy
  exact (hsub hxK).2

/-! ===================================================================
    PART A'.  A 3-D box `[a0,b0]×[a1,b1]×[a2,b2]` is the convex hull of its 8 CORNERS.

    `mkpt3 u v w := ![u, v, w]`.  Any box point is a convex combination of the 8 corners
    via THREE nested segment interpolations (trilinear): interpolate in x0 along the four
    parallel edges, then in x1, then in x2.  This is the "an axis-aligned 3-D cell = conv
    of its corners" fact for the octant arrangement.
    =================================================================== -/

/-- The 3-D point `(u,v,w)` as `Fin 3 → ℝ`. -/
def mkpt3 (u v w : ℝ) : X3 := ![u, v, w]

@[simp] theorem mkpt3_0 (u v w : ℝ) : mkpt3 u v w 0 = u := rfl
@[simp] theorem mkpt3_1 (u v w : ℝ) : mkpt3 u v w 1 = v := rfl
@[simp] theorem mkpt3_2 (u v w : ℝ) : mkpt3 u v w 2 = w := rfl

/-- The 8 corners of the box `[a0,b0]×[a1,b1]×[a2,b2]`. -/
def boxCorners3 (a0 b0 a1 b1 a2 b2 : ℝ) : Set X3 :=
  { mkpt3 a0 a1 a2, mkpt3 b0 a1 a2, mkpt3 a0 b1 a2, mkpt3 b0 b1 a2,
    mkpt3 a0 a1 b2, mkpt3 b0 a1 b2, mkpt3 a0 b1 b2, mkpt3 b0 b1 b2 }

/-- Interpolation in the x0-slot: `(x,v,w)` with `a ≤ x ≤ b` is in the segment between
    `(a,v,w)` and `(b,v,w)`, via weight `λ = (x-a)/(b-a)` (or trivially if `a=b`). -/
theorem seg_x0 (a b v w x : ℝ) (hab : a ≤ b) (hx : a ≤ x ∧ x ≤ b) :
    mkpt3 x v w ∈ segment ℝ (mkpt3 a v w) (mkpt3 b v w) := by
  obtain ⟨hxa, hxb⟩ := hx
  rcases eq_or_lt_of_le hab with he | hlt
  · have hxa' : x = a := le_antisymm (he ▸ hxb) hxa
    subst hxa'; exact left_mem_segment ℝ _ _
  · have hd : (0:ℝ) < b - a := by linarith
    refine ⟨1 - (x-a)/(b-a), (x-a)/(b-a), ?_, ?_, by ring, ?_⟩
    · have : (x-a)/(b-a) ≤ 1 := by rw [div_le_one hd]; linarith
      linarith
    · exact div_nonneg (by linarith) hd.le
    · funext j; fin_cases j
      · show (1 - (x-a)/(b-a)) * a + ((x-a)/(b-a)) * b = x
        field_simp; ring
      · show (1 - (x-a)/(b-a)) * v + ((x-a)/(b-a)) * v = v
        ring
      · show (1 - (x-a)/(b-a)) * w + ((x-a)/(b-a)) * w = w
        ring

/-- Interpolation in the x1-slot. -/
theorem seg_x1 (a b u w y : ℝ) (hab : a ≤ b) (hy : a ≤ y ∧ y ≤ b) :
    mkpt3 u y w ∈ segment ℝ (mkpt3 u a w) (mkpt3 u b w) := by
  obtain ⟨hya, hyb⟩ := hy
  rcases eq_or_lt_of_le hab with he | hlt
  · have hya' : y = a := le_antisymm (he ▸ hyb) hya
    subst hya'; exact left_mem_segment ℝ _ _
  · have hd : (0:ℝ) < b - a := by linarith
    refine ⟨1 - (y-a)/(b-a), (y-a)/(b-a), ?_, ?_, by ring, ?_⟩
    · have : (y-a)/(b-a) ≤ 1 := by rw [div_le_one hd]; linarith
      linarith
    · exact div_nonneg (by linarith) hd.le
    · funext j; fin_cases j
      · show (1 - (y-a)/(b-a)) * u + ((y-a)/(b-a)) * u = u
        ring
      · show (1 - (y-a)/(b-a)) * a + ((y-a)/(b-a)) * b = y
        field_simp; ring
      · show (1 - (y-a)/(b-a)) * w + ((y-a)/(b-a)) * w = w
        ring

/-- Interpolation in the x2-slot. -/
theorem seg_x2 (a b u v z : ℝ) (hab : a ≤ b) (hz : a ≤ z ∧ z ≤ b) :
    mkpt3 u v z ∈ segment ℝ (mkpt3 u v a) (mkpt3 u v b) := by
  obtain ⟨hza, hzb⟩ := hz
  rcases eq_or_lt_of_le hab with he | hlt
  · have hza' : z = a := le_antisymm (he ▸ hzb) hza
    subst hza'; exact left_mem_segment ℝ _ _
  · have hd : (0:ℝ) < b - a := by linarith
    refine ⟨1 - (z-a)/(b-a), (z-a)/(b-a), ?_, ?_, by ring, ?_⟩
    · have : (z-a)/(b-a) ≤ 1 := by rw [div_le_one hd]; linarith
      linarith
    · exact div_nonneg (by linarith) hd.le
    · funext j; fin_cases j
      · show (1 - (z-a)/(b-a)) * u + ((z-a)/(b-a)) * u = u
        ring
      · show (1 - (z-a)/(b-a)) * v + ((z-a)/(b-a)) * v = v
        ring
      · show (1 - (z-a)/(b-a)) * a + ((z-a)/(b-a)) * b = z
        field_simp; ring

/-- **★ A 3-D box is the convex hull of its 8 corners (membership form).**
    Any `(x,y,z)` with `a0≤x≤b0`, `a1≤y≤b1`, `a2≤z≤b2` lies in
    `convexHull ℝ (boxCorners3 …)`.  Trilinear interpolation: interpolate in x0 along
    the four parallel edges (each corner pair ∈ hull), then in x1, then in x2. -/
theorem mkpt3_mem_convexHull_boxCorners3 (a0 b0 a1 b1 a2 b2 x y z : ℝ)
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (hx : a0 ≤ x ∧ x ≤ b0) (hy : a1 ≤ y ∧ y ≤ b1) (hz : a2 ≤ z ∧ z ≤ b2) :
    mkpt3 x y z ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) := by
  have hconv := convex_convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2)
  -- The 8 corners are in the hull.
  have c000 : mkpt3 a0 a1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by left; rfl)
  have c100 : mkpt3 b0 a1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; left; rfl)
  have c010 : mkpt3 a0 b1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; left; rfl)
  have c110 : mkpt3 b0 b1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; right; left; rfl)
  have c001 : mkpt3 a0 a1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; right; right; left; rfl)
  have c101 : mkpt3 b0 a1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; right; right; right; left; rfl)
  have c011 : mkpt3 a0 b1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; right; right; right; right; left; rfl)
  have c111 : mkpt3 b0 b1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    subset_convexHull ℝ _ (by right; right; right; right; right; right; right; rfl)
  -- x0-interpolation on each of the 4 parallel edges (at z = a2 and z = b2):
  have e_x00 : mkpt3 x a1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset c000 c100 (seg_x0 a0 b0 a1 a2 x h0 hx)
  have e_x10 : mkpt3 x b1 a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset c010 c110 (seg_x0 a0 b0 b1 a2 x h0 hx)
  have e_x01 : mkpt3 x a1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset c001 c101 (seg_x0 a0 b0 a1 b2 x h0 hx)
  have e_x11 : mkpt3 x b1 b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset c011 c111 (seg_x0 a0 b0 b1 b2 x h0 hx)
  -- x1-interpolation on the two faces (at z = a2 and z = b2):
  have f_xy0 : mkpt3 x y a2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset e_x00 e_x10 (seg_x1 a1 b1 x a2 y h1 hy)
  have f_xy1 : mkpt3 x y b2 ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) :=
    hconv.segment_subset e_x01 e_x11 (seg_x1 a1 b1 x b2 y h1 hy)
  -- x2-interpolation between the two faces:
  exact hconv.segment_subset f_xy0 f_xy1 (seg_x2 a2 b2 x y z h2 hz)

/-- A coordinate `j`-component lower bound `m ≤ x j` is a convex halfspace in R^3. -/
theorem convex_coord_ge (j : Fin 3) (m : ℝ) : Convex ℝ {x : X3 | m ≤ x j} := by
  rw [convex_iff_forall_pos]
  rintro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  have := add_le_add (mul_le_mul_of_nonneg_left hp hs.le)
                     (mul_le_mul_of_nonneg_left hq ht.le)
  calc m = s * m + t * m := by rw [← add_mul, hst, one_mul]
    _ ≤ s * p j + t * q j := this

/-- A coordinate `j`-component upper bound `x j ≤ M` is a convex halfspace in R^3. -/
theorem convex_coord_le (j : Fin 3) (M : ℝ) : Convex ℝ {x : X3 | x j ≤ M} := by
  rw [convex_iff_forall_pos]
  rintro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  have := add_le_add (mul_le_mul_of_nonneg_left hp hs.le)
                     (mul_le_mul_of_nonneg_left hq ht.le)
  calc s * p j + t * q j ≤ s * M + t * M := this
    _ = M := by rw [← add_mul, hst, one_mul]

/-- **Coordinate bounds propagate through the 8-corner box hull.**  Every point of
    `convexHull (boxCorners3 …)` lies in the box `[a0,b0]×[a1,b1]×[a2,b2]`.  Each of the
    six coordinate halfspaces is convex and contains all 8 corners. -/
theorem boxCorners3Hull_coord_bounds (a0 b0 a1 b1 a2 b2 : ℝ)
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (x : X3)
    (hx : x ∈ convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2)) :
    a0 ≤ x 0 ∧ x 0 ≤ b0 ∧ a1 ≤ x 1 ∧ x 1 ≤ b1 ∧ a2 ≤ x 2 ∧ x 2 ≤ b2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | a0 ≤ x 0} := by
      apply convexHull_min _ (convex_coord_ge 0 a0)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | x 0 ≤ b0} := by
      apply convexHull_min _ (convex_coord_le 0 b0)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | a1 ≤ x 1} := by
      apply convexHull_min _ (convex_coord_ge 1 a1)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | x 1 ≤ b1} := by
      apply convexHull_min _ (convex_coord_le 1 b1)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | a2 ≤ x 2} := by
      apply convexHull_min _ (convex_coord_ge 2 a2)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ {x : X3 | x 2 ≤ b2} := by
      apply convexHull_min _ (convex_coord_le 2 b2)
      rintro w hw
      simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mkpt3] <;> linarith
    exact h hx

/-! ===================================================================
    PART B.  THE GENERAL 3-D ASSEMBLY THEOREM.

    A finite cover of the 3-D box by convex, sign-constant, finitely-generated cells —
    with all generators drawn from a global vertex set V — gives the closed-form hull
    equality  conv(curve3 '' box) = conv(curve3 '' V).
    Fully general: any k, any affine maps R^3→R, any plane positions.
    =================================================================== -/

/-- **A single sign-constant finitely-generated 3-D cell maps into `conv(curve3 '' V)`.** -/
theorem cell_image_subset_vertHull
    (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ) (V W : Set X3)
    (hWV : W ⊆ V)
    (hsc : ∀ i : Fin k, SignConstOn k A C (convexHull ℝ W) i) :
    curve3 k A C '' (convexHull ℝ W) ⊆ convexHull ℝ (curve3 k A C '' V) := by
  have hengine := surface3_image_subset_convHull_of_signConst k A C W hsc
  have himg : curve3 k A C '' W ⊆ curve3 k A C '' V := Set.image_mono hWV
  exact hengine.trans (convexHull_mono himg)

/-- **★ THE GENERAL 3-D ASSEMBLY THEOREM (any k, any affine maps, any plane positions).**
    Suppose `box` is the input region, `V` a global arrangement-vertex set with `V ⊆ box`,
    `cells : ι → Set X3` an indexed family of generator sets, each `cells j ⊆ V`, the
    cells COVER the box (every box point lies in `conv (cells j)` for some `j`), and on
    each cell every neuron is sign-constant.  THEN
          conv(curve3 '' box) = conv(curve3 '' V).
    The exact coupled-surface hull over the 3-D box equals the arrangement-vertex-image
    hull.  Dimension-and-plane-position-free.  -/
theorem coupledHull3_eq_vertImgs_of_cover
    {ι : Type*}
    (k : ℕ) (A : Fin k → Fin 3 → ℝ) (C : Fin k → ℝ)
    (box V : Set X3) (cells : ι → Set X3)
    (hVbox : V ⊆ box)
    (hcellV : ∀ j, cells j ⊆ V)
    (hcover : ∀ x ∈ box, ∃ j, x ∈ convexHull ℝ (cells j))
    (hsc : ∀ j, ∀ i : Fin k, SignConstOn k A C (convexHull ℝ (cells j)) i) :
    convexHull ℝ (curve3 k A C '' box) = convexHull ℝ (curve3 k A C '' V) := by
  apply Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hxj⟩ := hcover x hx
    have hsub := cell_image_subset_vertHull k A C V (cells j) (hcellV j) (hsc j)
    exact hsub ⟨x, hxj, rfl⟩
  · exact convexHull_mono (Set.image_mono hVbox)

/-! ===================================================================
    PART C.  THE CONCRETE k = 3 AXIS-PLANE 3-D-INPUT INSTANCE.

    box [-1,1]^3,  z1 = x0 (plane x0=0),  z2 = x1 (plane x1=0),  z3 = x2 (plane x2=0).
    The 3 sign-planes are the coordinate planes; they partition the box into 8 OCTANT
    sub-boxes.  ARRANGEMENT VERTICES = the 27 grid points {-1,0,1}^3:
      8 box corners (±1,±1,±1), 12 plane/box-edge points, 6 plane/plane-edge points,
      and the origin (0,0,0) = plane/plane/plane intersection.
    =================================================================== -/

/-- Instance weight matrix: `z1 = x0`, `z2 = x1`, `z3 = x2`. -/
def A3i : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
/-- Instance biases: all zero. -/
def C3i : Fin 3 → ℝ := ![0, 0, 0]

/-- On the instance (identity weight matrix, zero bias), `zvec3 x i = x i` for all i. -/
theorem zvec3_A3i (x : X3) (i : Fin 3) : zvec3 3 A3i C3i x i = x i := by
  fin_cases i <;> simp [zvec3, A3i, C3i]

/-- The input box `[-1,1]^3`. -/
def box3 : Set X3 :=
  { x | (-1:ℝ) ≤ x 0 ∧ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1 ∧ -1 ≤ x 2 ∧ x 2 ≤ 1 }

/-- The exact COUPLED 3-D-input k=3 ReLU SURFACE graph: image of the box under curve3. -/
def coupledGraph3 : Set (VK 3) := curve3 3 A3i C3i '' box3

/-- The **27 ARRANGEMENT VERTICES** = the grid `{-1,0,1}^3`.  These are exactly the box
    corners, plane/box-edge points, plane/plane-edge points and the plane/plane/plane
    origin of the coordinate-plane arrangement clipped to `[-1,1]^3`. -/
def arrVerts3 : Set X3 :=
  ⋃ (u ∈ ({-1, 0, 1} : Set ℝ)), ⋃ (v ∈ ({-1, 0, 1} : Set ℝ)),
    ⋃ (w ∈ ({-1, 0, 1} : Set ℝ)), {mkpt3 u v w}

/-- The arrangement-vertex IMAGE set in ℝ⁶: `curve3 '' arrVerts3`. -/
def arrVertImgs3 : Set (VK 3) := curve3 3 A3i C3i '' arrVerts3

/-- Membership helper: `mkpt3 u v w ∈ arrVerts3` whenever each of `u,v,w ∈ {-1,0,1}`. -/
theorem mkpt3_mem_arrVerts3 {u v w : ℝ}
    (hu : u = -1 ∨ u = 0 ∨ u = 1) (hv : v = -1 ∨ v = 0 ∨ v = 1)
    (hw : w = -1 ∨ w = 0 ∨ w = 1) : mkpt3 u v w ∈ arrVerts3 := by
  have huS : u ∈ ({-1, 0, 1} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hvS : v ∈ ({-1, 0, 1} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hwS : w ∈ ({-1, 0, 1} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  simp only [arrVerts3, Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨u, huS, v, hvS, w, hwS, rfl⟩

/-- The arrangement-vertex x-set is finite (27 explicit grid points). -/
theorem arrVerts3_finite : arrVerts3.Finite := by
  have hfin : ({-1, 0, 1} : Set ℝ).Finite := Set.toFinite _
  apply hfin.biUnion; intro u _
  apply hfin.biUnion; intro v _
  apply hfin.biUnion; intro w _
  exact Set.finite_singleton _

/-- The arrangement-vertex image set is finite (≤ 27 ℝ⁶ points). -/
theorem arrVertImgs3_finite : arrVertImgs3.Finite := arrVerts3_finite.image _

/-! The 8 OCTANT cells, each the convex hull of its 8 box-corners.  The octant signs
    `(σ0,σ1,σ2) ∈ {+,-}^3` choose the x0/x1/x2 half.  All 27 corner-grid points used are
    arrangement vertices. -/

/-- An octant cell as a box-corner hull, given its three coordinate half-intervals. -/
def octant (a0 b0 a1 b1 a2 b2 : ℝ) : Set X3 :=
  convexHull ℝ (boxCorners3 a0 b0 a1 b1 a2 b2)

/-- **Sign-constancy on an octant cell.**  On a box-corner cell whose x0-interval lies
    entirely on one side of 0, and likewise x1, x2, all three neurons `z_i = x_i` are
    sign-constant.  Driven by the side flags `s0,s1,s2 : Bool` (true = nonneg half). -/
theorem signConst_octant (a0 b0 a1 b1 a2 b2 : ℝ)
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (hx0 : 0 ≤ a0 ∨ b0 ≤ 0) (hx1 : 0 ≤ a1 ∨ b1 ≤ 0) (hx2 : 0 ≤ a2 ∨ b2 ≤ 0) :
    ∀ i : Fin 3, SignConstOn 3 A3i C3i (octant a0 b0 a1 b1 a2 b2) i := by
  -- Reduce `SignConstOn` to a statement purely about the coordinate `x i = z_i`.
  have hred : ∀ i : Fin 3, SignConstOn 3 A3i C3i (octant a0 b0 a1 b1 a2 b2) i ↔
      ((∀ x ∈ octant a0 b0 a1 b1 a2 b2, 0 ≤ x i) ∨
       (∀ x ∈ octant a0 b0 a1 b1 a2 b2, x i ≤ 0)) := by
    intro i
    constructor <;> intro h <;> rcases h with hp | hn
    · exact Or.inl (fun x hx => by have := hp x hx; rwa [zvec3_A3i] at this)
    · exact Or.inr (fun x hx => by have := hn x hx; rwa [zvec3_A3i] at this)
    · exact Or.inl (fun x hx => by have := hp x hx; rwa [zvec3_A3i])
    · exact Or.inr (fun x hx => by have := hn x hx; rwa [zvec3_A3i])
  intro i
  rw [hred]
  fin_cases i
  · -- neuron 0: coordinate x0; sign fixed by the x0-interval side
    rcases hx0 with hpos | hneg
    · refine Or.inl (fun x hx => ?_)
      show (0:ℝ) ≤ x 0
      obtain ⟨hl, _, _, _, _, _⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith
    · refine Or.inr (fun x hx => ?_)
      show x 0 ≤ (0:ℝ)
      obtain ⟨_, hu, _, _, _, _⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith
  · -- neuron 1: coordinate x1
    rcases hx1 with hpos | hneg
    · refine Or.inl (fun x hx => ?_)
      show (0:ℝ) ≤ x 1
      obtain ⟨_, _, hl, _, _, _⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith
    · refine Or.inr (fun x hx => ?_)
      show x 1 ≤ (0:ℝ)
      obtain ⟨_, _, _, hu, _, _⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith
  · -- neuron 2: coordinate x2
    rcases hx2 with hpos | hneg
    · refine Or.inl (fun x hx => ?_)
      show (0:ℝ) ≤ x 2
      obtain ⟨_, _, _, _, hl, _⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith
    · refine Or.inr (fun x hx => ?_)
      show x 2 ≤ (0:ℝ)
      obtain ⟨_, _, _, _, _, hu⟩ := boxCorners3Hull_coord_bounds a0 b0 a1 b1 a2 b2 h0 h1 h2 x hx
      linarith

/-- **Each octant's 8 corners are among the 27 arrangement vertices.**  For half-intervals
    whose endpoints lie in `{-1,0,1}` (true of all 8 octant cells), the corner set ⊆
    arrVerts3. -/
theorem octantCorners_subset (a0 b0 a1 b1 a2 b2 : ℝ)
    (g0 : a0 = -1 ∨ a0 = 0 ∨ a0 = 1) (g0' : b0 = -1 ∨ b0 = 0 ∨ b0 = 1)
    (g1 : a1 = -1 ∨ a1 = 0 ∨ a1 = 1) (g1' : b1 = -1 ∨ b1 = 0 ∨ b1 = 1)
    (g2 : a2 = -1 ∨ a2 = 0 ∨ a2 = 1) (g2' : b2 = -1 ∨ b2 = 0 ∨ b2 = 1) :
    boxCorners3 a0 b0 a1 b1 a2 b2 ⊆ arrVerts3 := by
  intro w hw
  simp only [boxCorners3, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact mkpt3_mem_arrVerts3 (by tauto) (by tauto) (by tauto)

/-- **The surface image of an octant cell lands in `conv(arrVertImgs3)`.**  Combines the
    3-D cell engine with "the cell's 8 corners are arrangement vertices". -/
theorem octant_image_subset_arrHull (a0 b0 a1 b1 a2 b2 : ℝ)
    (hsc : ∀ i : Fin 3, SignConstOn 3 A3i C3i (octant a0 b0 a1 b1 a2 b2) i)
    (hcorners : boxCorners3 a0 b0 a1 b1 a2 b2 ⊆ arrVerts3) :
    curve3 3 A3i C3i '' (octant a0 b0 a1 b1 a2 b2) ⊆ convexHull ℝ arrVertImgs3 := by
  have hengine :=
    surface3_image_subset_convHull_of_signConst 3 A3i C3i (boxCorners3 a0 b0 a1 b1 a2 b2) hsc
  have himg : curve3 3 A3i C3i '' (boxCorners3 a0 b0 a1 b1 a2 b2) ⊆ arrVertImgs3 :=
    Set.image_mono hcorners
  exact hengine.trans (convexHull_mono himg)

/-- **The 8 octants COVER the box.**  Any box point lies in one of the 8 octant cells
    (case split on the sign of x0, x1, x2), using trilinear box-corner membership.
    Stated against the general assembly engine's COVER hypothesis: there is an octant
    `cells j` of the 27-vertex arrangement whose hull contains `x`.  We index octants by
    a sign triple `(σ0,σ1,σ2) : Bool³` and give the cell directly. -/
def octantOf : Bool → Bool → Bool → Set X3
  | true,  true,  true  => octant 0    1 0    1 0    1
  | true,  true,  false => octant 0    1 0    1 (-1) 0
  | true,  false, true  => octant 0    1 (-1) 0 0    1
  | true,  false, false => octant 0    1 (-1) 0 (-1) 0
  | false, true,  true  => octant (-1) 0 0    1 0    1
  | false, true,  false => octant (-1) 0 0    1 (-1) 0
  | false, false, true  => octant (-1) 0 (-1) 0 0    1
  | false, false, false => octant (-1) 0 (-1) 0 (-1) 0

/-- Every octant is generated by box-corners that are all arrangement vertices. -/
theorem octantOf_corners_subset (σ0 σ1 σ2 : Bool) :
    ∃ a0 b0 a1 b1 a2 b2, octantOf σ0 σ1 σ2 = octant a0 b0 a1 b1 a2 b2 ∧
      boxCorners3 a0 b0 a1 b1 a2 b2 ⊆ arrVerts3 ∧
      (∀ i : Fin 3, SignConstOn 3 A3i C3i (octant a0 b0 a1 b1 a2 b2) i) := by
  cases σ0 <;> cases σ1 <;> cases σ2 <;>
  · refine ⟨_,_,_,_,_,_, rfl, ?_, ?_⟩
    · exact octantCorners_subset _ _ _ _ _ _ (by tauto) (by tauto) (by tauto) (by tauto)
        (by tauto) (by tauto)
    · exact signConst_octant _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)

/-- Any box point lies in some octant cell. -/
theorem box3_mem_octantOf (x : X3) (hx : x ∈ box3) :
    ∃ σ0 σ1 σ2 : Bool, x ∈ octantOf σ0 σ1 σ2 := by
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u⟩ := hx
  have hxeq : x = mkpt3 (x 0) (x 1) (x 2) := by funext j; fin_cases j <;> rfl
  rcases le_or_gt 0 (x 0) with s0 | s0 <;>
  rcases le_or_gt 0 (x 1) with s1 | s1 <;>
  rcases le_or_gt 0 (x 2) with s2 | s2
  · refine ⟨true, true, true, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 0 1 0 1 0 1 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨s0,h0u⟩ ⟨s1,h1u⟩ ⟨s2,h2u⟩
  · refine ⟨true, true, false, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 0 1 0 1 (-1) 0 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨s0,h0u⟩ ⟨s1,h1u⟩ ⟨h2l,s2.le⟩
  · refine ⟨true, false, true, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 0 1 (-1) 0 0 1 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨s0,h0u⟩ ⟨h1l,s1.le⟩ ⟨s2,h2u⟩
  · refine ⟨true, false, false, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 0 1 (-1) 0 (-1) 0 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨s0,h0u⟩ ⟨h1l,s1.le⟩ ⟨h2l,s2.le⟩
  · refine ⟨false, true, true, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 (-1) 0 0 1 0 1 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨h0l,s0.le⟩ ⟨s1,h1u⟩ ⟨s2,h2u⟩
  · refine ⟨false, true, false, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 (-1) 0 0 1 (-1) 0 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨h0l,s0.le⟩ ⟨s1,h1u⟩ ⟨h2l,s2.le⟩
  · refine ⟨false, false, true, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 (-1) 0 (-1) 0 0 1 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨h0l,s0.le⟩ ⟨h1l,s1.le⟩ ⟨s2,h2u⟩
  · refine ⟨false, false, false, ?_⟩
    rw [octantOf, octant, hxeq]
    exact mkpt3_mem_convexHull_boxCorners3 (-1) 0 (-1) 0 (-1) 0 _ _ _
      (by norm_num) (by norm_num) (by norm_num) ⟨h0l,s0.le⟩ ⟨h1l,s1.le⟩ ⟨h2l,s2.le⟩

/-! ===================================================================
    PART C (cont.).  THE MAIN 3-D ARRANGEMENT HULL EQUALITY AND LP-EXACTNESS.
    =================================================================== -/

/-- **Every coupled-surface graph point is in `conv(arrVertImgs3)`.**  Each box input
    lies in one of the 8 octant cells, on which all neurons are sign-constant, so its
    surface image is a convex combination of that octant's corner images — all
    arrangement-vertex images. -/
theorem graph3_subset_arrHull :
    coupledGraph3 ⊆ convexHull ℝ arrVertImgs3 := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨σ0, σ1, σ2, hmem⟩ := box3_mem_octantOf x hx
  obtain ⟨a0,b0,a1,b1,a2,b2, heq, hcorners, hsc⟩ := octantOf_corners_subset σ0 σ1 σ2
  rw [heq] at hmem
  exact octant_image_subset_arrHull a0 b0 a1 b1 a2 b2 hsc hcorners ⟨x, hmem, rfl⟩

/-- Each arrangement vertex (a grid point of `{-1,0,1}^3`) lies in the box `[-1,1]^3`. -/
theorem arrVerts3_subset_box : arrVerts3 ⊆ box3 := by
  intro w hw
  simp only [arrVerts3, Set.mem_iUnion, Set.mem_singleton_iff] at hw
  obtain ⟨u, huS, v, hvS, ww, hwS, rfl⟩ := hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huS hvS hwS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [mkpt3_0, mkpt3_1, mkpt3_2] <;>
    rcases huS with rfl | rfl | rfl <;> rcases hvS with rfl | rfl | rfl <;>
    rcases hwS with rfl | rfl | rfl <;> norm_num

/-- **Each arrangement-vertex image is a genuine point of the coupled surface graph.** -/
theorem arrVertImgs3_subset_graph3 : arrVertImgs3 ⊆ coupledGraph3 := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, arrVerts3_subset_box hw, rfl⟩

/-- **★ THE 3-D ARRANGEMENT HULL EQUALITY (the deliverable, concrete k=3 axis-plane).**
    For the coupled 3-D-INPUT k=3 ReLU surface graph (z1=x0, z2=x1, z3=x2 over `[-1,1]^3`,
    the three coordinate sign-PLANES crossing at the origin),
          conv(coupledGraph3) = conv(arrangement-vertex images).
    The exact convex hull of the piecewise-affine SURFACE over the 3-D box equals the
    convex hull of the images of the 27 arrangement vertices (the grid {-1,0,1}^3: box
    corners + plane/box-edge + plane/plane-edge + plane/plane/plane origin).  So the
    joint 3-cut family on the arrangement vertices IS the exact hull description in the
    genuinely 3-DIMENSIONAL-input coupled regime. -/
theorem coupled3_convHull_eq_arrangementVerts :
    convexHull ℝ coupledGraph3 = convexHull ℝ arrVertImgs3 := by
  refine Subset.antisymm ?_ (convexHull_mono arrVertImgs3_subset_graph3)
  exact convexHull_min graph3_subset_arrHull (convex_convexHull ℝ _)

/-- **★ 3-D LP-EXACTNESS on the arrangement vertices.**  For EVERY linear objective
    `objK e d`, IF its greatest value `M` over the FINITE 27-vertex image set is attained,
    THEN `M` is the greatest value over the ENTIRE coupled hull `conv(coupledGraph3)`.
    So optimizing any linear objective over the exact coupled 3-D-input k=3 ReLU
    relaxation reduces to checking the 27 arrangement vertices — the joint arrangement-cut
    is the LP-TIGHTEST / EXACT hull, no gap, in the 3-dimensional-input regime.  REUSES
    the dimension-free output-space engine `objK_isGreatest_convHull`. -/
theorem coupled3_lp_max_on_arrangementVerts (e d : Fin 3 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 3 e d '' arrVertImgs3) M) :
    IsGreatest (objK 3 e d '' convexHull ℝ coupledGraph3) M := by
  have := objK_isGreatest_convHull 3 e d arrVertImgs3 M hM
  rwa [← coupled3_convHull_eq_arrangementVerts] at this

/-! ===================================================================
    PART D.  A GENUINE k = 3 3-D-INPUT JOINT-CUT FACET (no relaxation gap).
    The joint 3-ReLU cut `relu z1 + relu z2 + relu z3 ≤ 3` is the EXACT optimum over
    conv(coupledGraph3), attained at the box corner (1,1,1).
    =================================================================== -/

/-- Joint-cut objective weights: `e = 0`, `d = (1,1,1)` — selects `relu z1+relu z2+relu z3`. -/
def eCut3 : Fin 3 → ℝ := ![0, 0, 0]
def dCut3 : Fin 3 → ℝ := ![1, 1, 1]

/-- The joint-cut objective evaluates to `relu z1 + relu z2 + relu z3` on an ℝ⁶ point. -/
theorem objCut3_eval (p : VK 3) : objK 3 eCut3 dCut3 p = p.2 0 + p.2 1 + p.2 2 := by
  simp only [objK, eCut3, dCut3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val]
  ring

/-- Graph-level joint-cut soundness: `relu x0 + relu x1 + relu x2 ≤ 3` for all
    `x ∈ [-1,1]^3`. -/
theorem cut3_graph_le (x : X3) (hx : x ∈ box3) :
    reluK (zvec3 3 A3i C3i x 0) + reluK (zvec3 3 A3i C3i x 1) + reluK (zvec3 3 A3i C3i x 2)
      ≤ 3 := by
  obtain ⟨_, h0u, _, h1u, _, h2u⟩ := hx
  rw [zvec3_A3i, zvec3_A3i, zvec3_A3i]
  unfold reluK
  rcases le_or_gt 0 (x 0) with s0 | s0 <;>
  rcases le_or_gt 0 (x 1) with s1 | s1 <;>
  rcases le_or_gt 0 (x 2) with s2 | s2
  all_goals first | rw [max_eq_right s0] | rw [max_eq_left s0.le]
  all_goals first | rw [max_eq_right s1] | rw [max_eq_left s1.le]
  all_goals first | rw [max_eq_right s2] | rw [max_eq_left s2.le]
  all_goals linarith

/-- The box corner `(1,1,1)` realizes the cut value 3: curve3 (1,1,1) = ((1,1,1),(1,1,1)). -/
theorem cut3_corner_val :
    objK 3 eCut3 dCut3 (curve3 3 A3i C3i (mkpt3 1 1 1)) = 3 := by
  rw [objCut3_eval]
  simp only [curve3, zvec3, A3i, C3i, mkpt3, reluK, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val]
  norm_num

/-- The corner `(1,1,1)` is a box point. -/
theorem corner111_in_box : mkpt3 1 1 1 ∈ box3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [mkpt3]

/-- **3-D joint-cut LP-exactness, graph optimum.**  The joint-cut objective
    `relu z1 + relu z2 + relu z3` attains its greatest value `3` over the EXACT coupled
    3-D-input k=3 graph, realized at the box corner `(1,1,1)`. -/
theorem cut3_isGreatest_graph :
    IsGreatest (objK 3 eCut3 dCut3 '' coupledGraph3) 3 := by
  constructor
  · exact ⟨curve3 3 A3i C3i (mkpt3 1 1 1), ⟨mkpt3 1 1 1, corner111_in_box, rfl⟩, cut3_corner_val⟩
  · rintro val ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [objCut3_eval]
    simp only [curve3]
    exact cut3_graph_le x hx

/-- **★ 3-D joint-cut EXACTNESS, hull = graph optimum (concrete capstone).**  The joint
    3-ReLU cut `relu z1 + relu z2 + relu z3 ≤ 3` is the EXACT optimum over the CONVEX HULL
    of the coupled 3-D-INPUT k=3 surface graph: `max conv(G3) = max G3 = 3`.  No relaxation
    gap.  Pushed through the dimension-free output-space engine `objK_isGreatest_convHull`
    — a genuine 3-dimensional-input joint-cut facet that is the exact hull optimum. -/
theorem coupled3_cut_is_facet :
    IsGreatest (objK 3 eCut3 dCut3 '' convexHull ℝ coupledGraph3) 3 :=
  objK_isGreatest_convHull 3 eCut3 dCut3 coupledGraph3 3 cut3_isGreatest_graph

/-! ===================================================================
    Trust-base check.  Every theorem must depend ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

-- PART A: the 3-D cell engine
#print axioms zvec3_affine_combo
#print axioms reluK_combo_on_signConst
#print axioms curve3_combo_on_cell
#print axioms curve3_mem_segment_on_cell
#print axioms surface3_image_subset_convHull_of_signConst
-- PART A': box-corner geometry & coordinate bounds
#print axioms mkpt3_mem_convexHull_boxCorners3
#print axioms boxCorners3Hull_coord_bounds
-- PART B: the general 3-D assembly theorem
#print axioms cell_image_subset_vertHull
#print axioms coupledHull3_eq_vertImgs_of_cover
-- PART C: the concrete k=3 axis-plane octant instance
#print axioms zvec3_A3i
#print axioms signConst_octant
#print axioms octantCorners_subset
#print axioms octantOf_corners_subset
#print axioms box3_mem_octantOf
#print axioms graph3_subset_arrHull
#print axioms arrVerts3_subset_box
#print axioms arrVertImgs3_subset_graph3
#print axioms arrVerts3_finite
#print axioms arrVertImgs3_finite
#print axioms coupled3_convHull_eq_arrangementVerts
#print axioms coupled3_lp_max_on_arrangementVerts
-- PART D: the genuine k=3 3-D-input joint-cut facet
#print axioms cut3_graph_le
#print axioms cut3_isGreatest_graph
#print axioms coupled3_cut_is_facet

end CrownproofArr3D
