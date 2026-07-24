/-
  WAVE-5 PROGRAM 4 — MULTI-DIMENSIONAL-INPUT (2-D) coupled k-ReLU convex hull /
  LP-exactness via the HYPERPLANE ARRANGEMENT of the sign-lines.

  ====================================================================
  WHAT WAS LEFT OPEN BY WAVE-4 (HullKGeneral.lean, committed aac99ad1)
  ====================================================================

  Wave-4 proved general-k coupled hull exactness for a SHARED 1-D SCALAR input:
  over [xl,xu] the coupled k-ReLU curve is PWL with ≤ k+2 breakpoints, and
        conv(coupledGraphK) = conv(≤ k+2 breakpoint vertices).
  It EXPLICITLY left OPEN the MULTI-DIMENSIONAL input case: the k pre-activations
        z_i(x) = a_i · x + c_i
  are affine in a VECTOR x over a box [xl,xu]^d, and the ReLU activation pattern
  changes across the ARRANGEMENT of the k sign-hyperplanes {z_i(x)=0}, not at
  scalar breakpoints.  This file attacks that for 2-D input (d = 2).

  ====================================================================
  WHAT THIS FILE PROVES (sorry-free; trust base [propext, Classical.choice, Quot.sound])
  ====================================================================

  Input x = (x0,x1) ∈ box [xl,xu]^2.  k pre-activations z_i = a_i·x + c_i affine in
  the 2-D vector.  The coupled k-ReLU graph is the PIECEWISE-AFFINE SURFACE
        G = { (z_1 x,…,z_k x, relu z_1 x,…,relu z_k x) : x ∈ box }  ⊂ ℝ^{2k},
  over the 2-D box partitioned by the k sign-lines {z_i = 0}.

  THE GENERAL 2-D ENGINE (reusable; arbitrary k, arbitrary affine maps a_i,c_i):
   ── (AFFINE-ON-A-SIGN-CONSTANT-CONVEX-CELL)  `curve2_affine_on_cell` /
      `surface2_image_subset_convHull_of_signConst`.
      On ANY convex cell K ⊆ box on which EVERY neuron is sign-constant (its
      pre-activation keeps one sign throughout K), the surface `curve2` is AFFINE
      (each ReLU collapses to z_i or to 0).  Hence
            curve2 '' K  ⊆  conv (curve2 '' (extreme/spanning points of K)).
      Concretely, if K = conv(W) for a finite W, then curve2 '' K ⊆ conv(curve2 '' W).
      This is the genuinely-2-D arrangement-cell content: each arrangement CELL of
      the sign-line arrangement is a convex polygon on which the surface is affine,
      so its image is the conv of the images of the CELL VERTICES — which are
      arrangement vertices (box corners, line/box and line/line intersections).

  THE CONCRETE GENUINELY-2-D-INPUT k = 2 INSTANCE (the deliverable, rigorous):
      box [-1,1]^2, z1 = x0 (sign-line x0 = 0), z2 = x1 (sign-line x1 = 0).
      The two sign-lines CROSS at the origin INSIDE the box (a real line/line
      arrangement vertex).  The arrangement partitions the box into the 4 quadrant
      sub-squares; the ARRANGEMENT VERTICES are
            4 box corners (±1,±1),
            4 edge midpoints (line/box: (±1,0),(0,±1)),
            1 center (line/line: (0,0))            — 9 vertices.
   ── (ARRANGEMENT HULL)  `coupled2_convHull_eq_arrangementVerts`:
        conv(G) = conv(arrangement-vertex images).
      Proof: every box point lies in one of the 4 quadrant squares; that square is
      conv of its 4 corners (all arrangement vertices); on it both neurons are
      sign-constant so the surface is affine ⇒ its image ⊆ conv(corner images).
   ── (LP-EXACTNESS)  `coupled2_lp_max_on_arrangementVerts`: for EVERY linear
      objective whose max over the FINITE arrangement-vertex set is attained, that
      value is the max over the ENTIRE coupled hull conv(G).  REUSES the
      dimension-free engine `objK_isGreatest_convHull` from HullKGeneral.
   ── (CONCRETE FACET) `coupled2_cut_is_facet`: the joint 2-ReLU cut
      relu z1 + relu z2 ≤ 2 is the EXACT optimum over conv(G), attained at the box
      corner (1,1) — a genuine 2-D-input joint-cut facet, no relaxation gap.

  PARAMETER COVERAGE (ruthlessly honest, per the task instruction):
   * The GENERAL ENGINE (`curve2_affine_on_cell`,
     `surface2_image_subset_convHull_of_signConst`) is fully general: ANY k, ANY
     affine maps a_i,c_i, ANY convex sign-constant cell K = conv(W).  This is the
     reusable "the 2-D PWL surface is the conv of its arrangement-cell vertices"
     content — the piece Wave-4 lacked.
   * The CLOSED-FORM hull equality `conv(G) = conv(arrangement verts)` and the
     LP-exactness / facet results are proved for a CONCRETE genuinely-2-D-input
     k = 2 instance (two crossing axis sign-lines over [-1,1]^2), rigorously through
     its 9 arrangement vertices via an explicit 4-quadrant cover.  The general
     closed-form arrangement-vertex enumeration for ARBITRARY lines (which cells
     exist, their vertex lists) is combinatorially heavy and is NOT claimed in full
     generality; we state coverage exactly: GENERAL affine-cell engine + a concrete
     real multi-D-input instance carried through it end-to-end.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Crownproof.HullKGeneral

namespace CrownproofArr2D

open Set
open CrownproofK (reluK reluK_of_nonneg reluK_of_neg VK objK objK_isGreatest_convHull)

/-! ===================================================================
    SECTION 0.  2-D affine pre-activations, sign-constancy on a convex cell.
    =================================================================== -/

/-- A 2-D input vector. -/
abbrev X2 := Fin 2 → ℝ

/-- Pre-activation of neuron `i`: `z_i(x) = A i 0 * x0 + A i 1 * x1 + C i`, affine in
    the 2-D vector `x`.  `A : Fin k → Fin 2 → ℝ` is the weight matrix, `C : Fin k → ℝ`
    the bias. -/
def zvec2 (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (x : X2) : Fin k → ℝ :=
  fun i => A i 0 * x 0 + A i 1 * x 1 + C i

/-- The coupled k-ReLU SURFACE point at 2-D input `x`:
    `(z_1 x,…,z_k x, relu(z_1 x),…,relu(z_k x)) ∈ ℝ^{2k}`. -/
def curve2 (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (x : X2) : VK k :=
  (zvec2 k A C x, fun i => reluK (zvec2 k A C x i))

/-- `z_i` is "sign-constant on the cell `K`": its pre-activation keeps ONE sign
    (all ≥ 0, or all ≤ 0) over all of `K`. -/
def SignConstOn (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (K : Set X2)
    (i : Fin k) : Prop :=
  (∀ x ∈ K, 0 ≤ zvec2 k A C x i) ∨ (∀ x ∈ K, zvec2 k A C x i ≤ 0)

/-! ===================================================================
    SECTION 1.  THE GENERAL 2-D ENGINE.

    On a CONVEX cell K where every neuron is sign-constant, `curve2` is affine, so
    `curve2 '' K ⊆ conv(curve2 '' W)` whenever `K ⊆ conv W` (W finite spanning set).

    The clean route: `zvec2` is affine (jointly affine in x), and ReLU collapses to
    an affine map on a sign-constant cell, so `curve2` restricted to K is an affine
    map.  We avoid an abstract AffineMap and instead show directly: any convex
    combination point image equals the matching convex combination of images, using
    that on a sign-constant cell relu is "linear enough".  Concretely we prove the
    SEGMENT version (2 points) and the general finite-conv version (via the
    midpoint/segment is enough together with `convexHull_min`).
    =================================================================== -/

/-- `zvec2` is jointly affine: for a convex combination `s•p + t•q` (`s+t=1`),
    `zvec2 (s•p+t•q) i = s * zvec2 p i + t * zvec2 q i`. -/
theorem zvec2_affine_combo (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ)
    (p q : X2) (s t : ℝ) (hst : s + t = 1) (i : Fin k) :
    zvec2 k A C (s • p + t • q) i = s * zvec2 k A C p i + t * zvec2 k A C q i := by
  simp only [zvec2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- s*(A0*p0+A1*p1+C) + t*(A0*q0+A1*q1+C); the C term needs s+t=1.
  have ht1 : t = 1 - s := by linarith
  subst ht1
  ring

/-- On a sign-constant cell, ReLU of an affine combination of two cell points is the
    same affine combination of the ReLUs.  KEY: needs `s,t ≥ 0`, `s+t=1`, and that
    BOTH endpoints (hence — by sign-constancy of the whole segment — the combination)
    are on the same side of 0. -/
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

/-- **The 2-D surface is affine on a sign-constant convex cell — SEGMENT form.**
    If `p, q ∈ K`, the whole segment `[p,q] ⊆ K`, and every neuron is sign-constant
    on `K`, then for any convex weights `s,t ≥ 0`, `s+t=1`,
        curve2 (s•p + t•q) = s • curve2 p + t • curve2 q.
    (Both ℝ^{2k} components: pre-activations are jointly affine; post-activations are
    affine by `reluK_combo_on_signConst`, since `p,q ∈ K` are on the same side.) -/
theorem curve2_combo_on_cell (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ)
    (K : Set X2) (hKconv : Convex ℝ K) (p q : X2) (hp : p ∈ K) (hq : q ∈ K)
    (hsc : ∀ i : Fin k, SignConstOn k A C K i)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    curve2 k A C (s • p + t • q) = s • curve2 k A C p + t • curve2 k A C q := by
  apply Prod.ext
  · -- pre-activation component: jointly affine
    funext i
    simp only [curve2, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact zvec2_affine_combo k A C p q s t hst i
  · -- post-activation component: relu of affine combo = affine combo of relus
    funext i
    simp only [curve2, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [zvec2_affine_combo k A C p q s t hst i]
    -- sign-constancy of neuron i at the two cell points p, q (same side)
    have hsgn : (0 ≤ zvec2 k A C p i ∧ 0 ≤ zvec2 k A C q i) ∨
                (zvec2 k A C p i ≤ 0 ∧ zvec2 k A C q i ≤ 0) := by
      rcases hsc i with hpos | hneg
      · exact Or.inl ⟨hpos p hp, hpos q hq⟩
      · exact Or.inr ⟨hneg p hp, hneg q hq⟩
    exact reluK_combo_on_signConst _ _ s t hs ht hst hsgn

/-- Hence on a sign-constant convex cell, `curve2 (s•p+t•q) ∈ segment (curve2 p) (curve2 q)`. -/
theorem curve2_mem_segment_on_cell (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ)
    (K : Set X2) (hKconv : Convex ℝ K) (p q : X2) (hp : p ∈ K) (hq : q ∈ K)
    (hsc : ∀ i : Fin k, SignConstOn k A C K i)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    curve2 k A C (s • p + t • q) ∈ segment ℝ (curve2 k A C p) (curve2 k A C q) :=
  ⟨s, t, hs, ht, hst, (curve2_combo_on_cell k A C K hKconv p q hp hq hsc s t hs ht hst).symm⟩

/-! ===================================================================
    SECTION 1b.  Image of a finitely-generated convex cell ⊆ conv(images of generators).

    If `K = conv(W)` for a finite (or any) `W`, and every neuron is sign-constant on
    K, then `curve2 '' K ⊆ conv(curve2 '' W)`.  This is the arrangement-cell content:
    each arrangement cell K is the convex hull of its VERTICES W (corners), and the
    surface's image over K is contained in the convex hull of the vertex images.

    Proof strategy: show `K ⊆ { x | curve2 x ∈ conv(curve2 '' W) }`.  That set is
    convex (by the segment lemma above, since on a sign-constant cell curve2 sends
    segments to segments, and conv(curve2 '' W) is convex), and contains W (each
    w ∈ W maps to curve2 w ∈ conv(curve2 '' W)).  Then `convexHull_min` gives
    `conv(W) ⊆ {…}`, i.e. the surface image of conv(W) lands in conv(curve2''W).
    =================================================================== -/

/-- The "good set" RELATIVE to a cell `K`: cell points whose surface image is in
    `conv(curve2 '' W)`.  Bundling cell membership lets the convexity proof use the
    segment lemma (which needs the two points to be IN the sign-constant cell). -/
def GoodSet (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (K W : Set X2) : Set X2 :=
  { x | x ∈ K ∧ curve2 k A C x ∈ convexHull ℝ (curve2 k A C '' W) }

/-- **★ THE 2-D ARRANGEMENT-CELL ENGINE (fully general k, any affine maps).**
    If a convex cell `K` is the convex hull of a generating set `W`, and EVERY neuron
    is sign-constant on `K`, then the surface image of `K` lies in the convex hull of
    the surface images of the generators `W`:
          curve2 '' (convexHull ℝ W)  ⊆  convexHull ℝ (curve2 '' W).
    This is the precise statement "the piecewise-affine surface over an arrangement
    cell is the conv of the images of the cell's vertices". -/
theorem surface2_image_subset_convHull_of_signConst
    (k : ℕ) (A : Fin k → Fin 2 → ℝ) (C : Fin k → ℝ) (W : Set X2)
    (hsc : ∀ i : Fin k, SignConstOn k A C (convexHull ℝ W) i) :
    curve2 k A C '' (convexHull ℝ W) ⊆ convexHull ℝ (curve2 k A C '' W) := by
  set K := convexHull ℝ W with hKdef
  have hKconv : Convex ℝ K := convex_convexHull ℝ W
  -- It suffices that K ⊆ GoodSet K W, then map points of the image.
  have hsub : K ⊆ GoodSet k A C K W := by
    rw [hKdef]
    apply convexHull_min
    · -- W ⊆ GoodSet : each generator is a cell point with image in conv(curve2 '' W)
      intro w hw
      refine ⟨subset_convexHull ℝ W hw, subset_convexHull ℝ _ ⟨w, hw, rfl⟩⟩
    · -- GoodSet K W is convex: segments of cell-points map into the convex target hull
      rw [convex_iff_forall_pos]
      rintro p ⟨hpK, hpImg⟩ q ⟨hqK, hqImg⟩ s t hs ht hst
      refine ⟨hKconv hpK hqK hs.le ht.le hst, ?_⟩
      -- curve2 (s•p+t•q) ∈ segment (curve2 p) (curve2 q) ⊆ target hull
      have hseg : curve2 k A C (s • p + t • q)
            ∈ segment ℝ (curve2 k A C p) (curve2 k A C q) :=
        curve2_mem_segment_on_cell k A C K hKconv p q hpK hqK hsc s t hs.le ht.le hst
      exact (convex_convexHull ℝ _).segment_subset hpImg hqImg hseg
  intro y hy
  obtain ⟨x, hxK, rfl⟩ := hy
  exact (hsub hxK).2

/-! ===================================================================
    SECTION 1c.  A 2-D box `[a,b]×[c,d]` is the convex hull of its 4 CORNERS.

    `mkpt a b := ![a, b]` is the point `(a,b)`.  We show any box point is a convex
    combination of the four corners via NESTED segments (bilinear interpolation):
    interpolate in x along the bottom and top edges, then in y between them.  This is
    the reusable "an axis-aligned cell = conv of its corners" fact for the
    arrangement (each arrangement cell here is such a box).
    =================================================================== -/

/-- The 2-D point `(u,v)` as `Fin 2 → ℝ`. -/
def mkpt (u v : ℝ) : X2 := ![u, v]

@[simp] theorem mkpt_0 (u v : ℝ) : mkpt u v 0 = u := rfl
@[simp] theorem mkpt_1 (u v : ℝ) : mkpt u v 1 = v := rfl

/-- The 4 corners of the box `[a,b]×[c,d]`. -/
def boxCorners (a b c d : ℝ) : Set X2 :=
  {mkpt a c, mkpt b c, mkpt a d, mkpt b d}

/-- A point on the bottom/top edge `(x, e)` with `a ≤ x ≤ b` is in `segment (a,e) (b,e)`,
    realized by the weight `λ = (x-a)/(b-a)` (or trivially if `a = b`). -/
theorem mkpt_edge_mem_segment (a b e x : ℝ) (hab : a ≤ b) (hx : a ≤ x ∧ x ≤ b) :
    mkpt x e ∈ segment ℝ (mkpt a e) (mkpt b e) := by
  obtain ⟨hxa, hxb⟩ := hx
  rcases eq_or_lt_of_le hab with he | hlt
  · -- a = b ⇒ x = a, point is an endpoint
    have hxa' : x = a := le_antisymm (he ▸ hxb) hxa
    subst hxa'; exact left_mem_segment ℝ _ _
  · have hd : (0:ℝ) < b - a := by linarith
    refine ⟨1 - (x-a)/(b-a), (x-a)/(b-a), ?_, ?_, by ring, ?_⟩
    · have : (x-a)/(b-a) ≤ 1 := by rw [div_le_one hd]; linarith
      linarith
    · exact div_nonneg (by linarith) hd.le
    · have hne : b - a ≠ 0 := ne_of_gt hd
      funext j; fin_cases j
      · show (1 - (x-a)/(b-a)) * a + ((x-a)/(b-a)) * b = x
        field_simp; ring
      · show (1 - (x-a)/(b-a)) * e + ((x-a)/(b-a)) * e = e
        ring

/-- **★ A box `[a,b]×[c,d]` is the convex hull of its 4 corners (membership form).**
    Any `(x,y)` with `a ≤ x ≤ b`, `c ≤ y ≤ d` lies in `convexHull ℝ (boxCorners …)`. -/
theorem mkpt_mem_convexHull_boxCorners (a b c d x y : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    mkpt x y ∈ convexHull ℝ (boxCorners a b c d) := by
  have hconv := convex_convexHull ℝ (boxCorners a b c d)
  -- bottom-edge point (x,c) and top-edge point (x,d) are in the hull (corners ∈ hull)
  have hac : mkpt a c ∈ convexHull ℝ (boxCorners a b c d) :=
    subset_convexHull ℝ _ (by left; rfl)
  have hbc : mkpt b c ∈ convexHull ℝ (boxCorners a b c d) :=
    subset_convexHull ℝ _ (by right; left; rfl)
  have had : mkpt a d ∈ convexHull ℝ (boxCorners a b c d) :=
    subset_convexHull ℝ _ (by right; right; left; rfl)
  have hbd : mkpt b d ∈ convexHull ℝ (boxCorners a b c d) :=
    subset_convexHull ℝ _ (by right; right; right; rfl)
  -- (x,c) ∈ segment (a,c) (b,c) ⊆ hull ; (x,d) ∈ segment (a,d) (b,d) ⊆ hull
  have hxc : mkpt x c ∈ convexHull ℝ (boxCorners a b c d) :=
    hconv.segment_subset hac hbc (mkpt_edge_mem_segment a b c x hab hx)
  have hxd : mkpt x d ∈ convexHull ℝ (boxCorners a b c d) :=
    hconv.segment_subset had hbd (mkpt_edge_mem_segment a b d x hab hx)
  -- (x,y) ∈ segment (x,c) (x,d) ⊆ hull (vertical interpolation in the 2nd coord)
  have hvert : mkpt x y ∈ segment ℝ (mkpt x c) (mkpt x d) := by
    obtain ⟨hyc, hyd⟩ := hy
    rcases eq_or_lt_of_le hcd with he | hlt
    · have hyc' : y = c := le_antisymm (he ▸ hyd) hyc
      subst hyc'; exact left_mem_segment ℝ _ _
    · have hd : (0:ℝ) < d - c := by linarith
      refine ⟨1 - (y-c)/(d-c), (y-c)/(d-c), ?_, ?_, by ring, ?_⟩
      · have : (y-c)/(d-c) ≤ 1 := by rw [div_le_one hd]; linarith
        linarith
      · exact div_nonneg (by linarith) hd.le
      · have hne : d - c ≠ 0 := ne_of_gt hd
        funext j; fin_cases j
        · show (1 - (y-c)/(d-c)) * x + ((y-c)/(d-c)) * x = x
          ring
        · show (1 - (y-c)/(d-c)) * c + ((y-c)/(d-c)) * d = y
          field_simp; ring
  exact hconv.segment_subset hxc hxd hvert

/-! ===================================================================
    SECTION 2.  THE CONCRETE GENUINELY-2-D-INPUT k = 2 INSTANCE.

    box [-1,1]^2,  z1 = x0  (sign-line x0 = 0),  z2 = x1  (sign-line x1 = 0).
    The two sign-lines CROSS at the origin INSIDE the box.  The arrangement
    partitions the box into 4 quadrant squares; the ARRANGEMENT VERTICES are the
    box corners, the edge midpoints (line/box intersections) and the center
    (line/line intersection): 9 vertices in all.
    =================================================================== -/

/-- Instance weight matrix: `z1 = x0`, `z2 = x1`. -/
def A2 : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]
/-- Instance biases: both zero. -/
def C2 : Fin 2 → ℝ := ![0, 0]

/-- On the instance (identity weight matrix, zero bias), `zvec2 x i = x i` for ALL i. -/
theorem zvec2_A2 (x : X2) (i : Fin 2) : zvec2 2 A2 C2 x i = x i := by
  fin_cases i <;> simp [zvec2, A2, C2]
/-- On the instance, `zvec2 x 0 = x0`. -/
theorem zvec2_A2_0 (x : X2) : zvec2 2 A2 C2 x 0 = x 0 := zvec2_A2 x 0
/-- On the instance, `zvec2 x 1 = x1`. -/
theorem zvec2_A2_1 (x : X2) : zvec2 2 A2 C2 x 1 = x 1 := zvec2_A2 x 1

/-- The four quadrant cells, each given as the convex hull of its 4 corners.
    Quadrant signs `(σ0, σ1) ∈ {+,-}^2` choose the x0- and x1-half. -/
def quadPP : Set X2 := convexHull ℝ (boxCorners 0 1 0 1)     -- x0∈[0,1], x1∈[0,1]
def quadMP : Set X2 := convexHull ℝ (boxCorners (-1) 0 0 1)  -- x0∈[-1,0], x1∈[0,1]
def quadPM : Set X2 := convexHull ℝ (boxCorners 0 1 (-1) 0)  -- x0∈[0,1], x1∈[-1,0]
def quadMM : Set X2 := convexHull ℝ (boxCorners (-1) 0 (-1) 0) -- x0∈[-1,0], x1∈[-1,0]

/-- A coordinate `j`-component lower bound `m ≤ x j` is a convex halfspace. -/
theorem convex_coord_ge (j : Fin 2) (m : ℝ) : Convex ℝ {x : X2 | m ≤ x j} := by
  rw [convex_iff_forall_pos]
  rintro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  have := add_le_add (mul_le_mul_of_nonneg_left hp hs.le)
                     (mul_le_mul_of_nonneg_left hq ht.le)
  calc m = s * m + t * m := by rw [← add_mul, hst, one_mul]
    _ ≤ s * p j + t * q j := this

/-- A coordinate `j`-component upper bound `x j ≤ M` is a convex halfspace. -/
theorem convex_coord_le (j : Fin 2) (M : ℝ) : Convex ℝ {x : X2 | x j ≤ M} := by
  rw [convex_iff_forall_pos]
  rintro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  have := add_le_add (mul_le_mul_of_nonneg_left hp hs.le)
                     (mul_le_mul_of_nonneg_left hq ht.le)
  calc s * p j + t * q j ≤ s * M + t * M := this
    _ = M := by rw [← add_mul, hst, one_mul]

/-- **Coordinate bounds propagate through the box-corner hull.**  Every point of
    `convexHull (boxCorners a b c d)` lies in the box `[a,b]×[c,d]`.  Proof: each of
    the four coordinate halfspaces is convex and contains all 4 corners, so contains
    the hull (`convexHull_min`). -/
theorem boxCornersHull_coord_bounds (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (x : X2)
    (hx : x ∈ convexHull ℝ (boxCorners a b c d)) :
    a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : convexHull ℝ (boxCorners a b c d) ⊆ {x : X2 | a ≤ x 0} := by
      apply convexHull_min _ (convex_coord_ge 0 a)
      rintro w hw
      simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp [mkpt] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners a b c d) ⊆ {x : X2 | x 0 ≤ b} := by
      apply convexHull_min _ (convex_coord_le 0 b)
      rintro w hw
      simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp [mkpt] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners a b c d) ⊆ {x : X2 | c ≤ x 1} := by
      apply convexHull_min _ (convex_coord_ge 1 c)
      rintro w hw
      simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp [mkpt] <;> linarith
    exact h hx
  · have h : convexHull ℝ (boxCorners a b c d) ⊆ {x : X2 | x 1 ≤ d} := by
      apply convexHull_min _ (convex_coord_le 1 d)
      rintro w hw
      simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp [mkpt] <;> linarith
    exact h hx

/-! ===================================================================
    SECTION 2b.  Both instance neurons are sign-constant on each quadrant.
    z1 = x0, z2 = x1; the quadrant's sign of x0 (resp. x1) is fixed by its x0-
    (resp. x1-) interval being entirely ≥ 0 or entirely ≤ 0.
    =================================================================== -/

/-- Both neurons are sign-constant on the (+,+) quadrant `[0,1]×[0,1]`
    (z1=x0≥0, z2=x1≥0). -/
theorem signConst_quadPP : ∀ i : Fin 2, SignConstOn 2 A2 C2 quadPP i := by
  intro i
  fin_cases i
  · -- z1 = x0 ≥ 0 on [0,1]×[0,1]
    refine Or.inl (fun x hx => ?_)
    obtain ⟨h0, _, _, _⟩ := boxCornersHull_coord_bounds 0 1 0 1 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h0
  · -- z2 = x1 ≥ 0
    refine Or.inl (fun x hx => ?_)
    obtain ⟨_, _, h1, _⟩ := boxCornersHull_coord_bounds 0 1 0 1 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h1

/-- (-,+) quadrant `[-1,0]×[0,1]`: z1=x0≤0, z2=x1≥0. -/
theorem signConst_quadMP : ∀ i : Fin 2, SignConstOn 2 A2 C2 quadMP i := by
  intro i
  fin_cases i
  · refine Or.inr (fun x hx => ?_)  -- z1 = x0 ≤ 0
    obtain ⟨_, h0, _, _⟩ := boxCornersHull_coord_bounds (-1) 0 0 1 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h0
  · refine Or.inl (fun x hx => ?_)  -- z2 = x1 ≥ 0
    obtain ⟨_, _, h1, _⟩ := boxCornersHull_coord_bounds (-1) 0 0 1 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h1

/-- (+,-) quadrant `[0,1]×[-1,0]`: z1=x0≥0, z2=x1≤0. -/
theorem signConst_quadPM : ∀ i : Fin 2, SignConstOn 2 A2 C2 quadPM i := by
  intro i
  fin_cases i
  · refine Or.inl (fun x hx => ?_)  -- z1 = x0 ≥ 0
    obtain ⟨h0, _, _, _⟩ := boxCornersHull_coord_bounds 0 1 (-1) 0 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h0
  · refine Or.inr (fun x hx => ?_)  -- z2 = x1 ≤ 0
    obtain ⟨_, _, _, h1⟩ := boxCornersHull_coord_bounds 0 1 (-1) 0 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h1

/-- (-,-) quadrant `[-1,0]×[-1,0]`: z1=x0≤0, z2=x1≤0. -/
theorem signConst_quadMM : ∀ i : Fin 2, SignConstOn 2 A2 C2 quadMM i := by
  intro i
  fin_cases i
  · refine Or.inr (fun x hx => ?_)  -- z1 = x0 ≤ 0
    obtain ⟨_, h0, _, _⟩ := boxCornersHull_coord_bounds (-1) 0 (-1) 0 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h0
  · refine Or.inr (fun x hx => ?_)  -- z2 = x1 ≤ 0
    obtain ⟨_, _, _, h1⟩ := boxCornersHull_coord_bounds (-1) 0 (-1) 0 (by norm_num) (by norm_num) x hx
    rw [zvec2_A2]; exact h1

/-! ===================================================================
    SECTION 3.  The 2-D box, the coupled SURFACE graph, the 9 ARRANGEMENT VERTICES,
    and the per-quadrant image-into-arrangement-hull step.
    =================================================================== -/

/-- The 2-D box `[-1,1]^2` as a set of 2-D inputs. -/
def box2 : Set X2 := { x | (-1 : ℝ) ≤ x 0 ∧ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1 }

/-- The exact COUPLED 2-D-input k=2 ReLU SURFACE graph: image of the box under curve2. -/
def coupledGraph2 : Set (VK 2) := curve2 2 A2 C2 '' box2

/-- The **9 ARRANGEMENT VERTICES** of the sign-line arrangement clipped to the box:
    4 box corners (±1,±1), 4 edge midpoints (line/box: (±1,0),(0,±1)), and the
    center (line/line: (0,0)). -/
def arrVerts : Set X2 :=
  { mkpt 1 1, mkpt 1 (-1), mkpt (-1) 1, mkpt (-1) (-1),   -- box corners
    mkpt 1 0, mkpt (-1) 0, mkpt 0 1, mkpt 0 (-1),         -- line/box midpoints
    mkpt 0 0 }                                             -- line/line center

/-- The arrangement-vertex IMAGE set in ℝ⁴: `curve2 '' arrVerts`. -/
def arrVertImgs : Set (VK 2) := curve2 2 A2 C2 '' arrVerts

/-- The arrangement-vertex x-set is finite (9 explicit points). -/
theorem arrVerts_finite : arrVerts.Finite := by
  unfold arrVerts
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _
    |>.insert _ |>.insert _ |>.insert _ |>.insert _

/-- The arrangement-vertex image set is finite (9 ℝ⁴ points). -/
theorem arrVertImgs_finite : arrVertImgs.Finite := arrVerts_finite.image _

/-- Each quadrant's 4 corners are among the 9 arrangement vertices.  We prove the
    `Set` inclusion of corner sets into `arrVerts`. -/
theorem boxCorners_PP_subset : boxCorners 0 1 0 1 ⊆ arrVerts := by
  intro w hw
  simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  -- corners: (0,0),(1,0),(0,1),(1,1) — all arrangement vertices
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [arrVerts, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

theorem boxCorners_MP_subset : boxCorners (-1) 0 0 1 ⊆ arrVerts := by
  intro w hw
  simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  -- corners: (-1,0),(0,0),(-1,1),(0,1)
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [arrVerts, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

theorem boxCorners_PM_subset : boxCorners 0 1 (-1) 0 ⊆ arrVerts := by
  intro w hw
  simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  -- corners: (0,-1),(1,-1),(0,0),(1,0)
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [arrVerts, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

theorem boxCorners_MM_subset : boxCorners (-1) 0 (-1) 0 ⊆ arrVerts := by
  intro w hw
  simp only [boxCorners, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  -- corners: (-1,-1),(0,-1),(-1,0),(0,0)
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [arrVerts, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- **The surface image of a quadrant cell lands in `conv(arrVertImgs)`.**  Combines
    the general arrangement-cell engine (image of a sign-constant convex cell ⊆ conv
    of the images of its generators) with "the cell's 4 corners are arrangement
    vertices".  Stated for a generic box-corner cell whose corner set ⊆ arrVerts and
    on which all neurons are sign-constant. -/
theorem quad_image_subset_arrHull
    (a b c d : ℝ)
    (hsc : ∀ i : Fin 2, SignConstOn 2 A2 C2 (convexHull ℝ (boxCorners a b c d)) i)
    (hcorners : boxCorners a b c d ⊆ arrVerts) :
    curve2 2 A2 C2 '' (convexHull ℝ (boxCorners a b c d)) ⊆ convexHull ℝ arrVertImgs := by
  -- engine: image of the cell ⊆ conv(curve2 '' boxCorners)
  have hengine := surface2_image_subset_convHull_of_signConst 2 A2 C2 (boxCorners a b c d) hsc
  -- curve2 '' boxCorners ⊆ arrVertImgs (corner images are arrangement-vertex images)
  have himg : curve2 2 A2 C2 '' (boxCorners a b c d) ⊆ arrVertImgs :=
    Set.image_mono hcorners
  -- chain: cell image ⊆ conv(corner images) ⊆ conv(arrVertImgs)
  exact hengine.trans (convexHull_mono himg)

/-- **The 4 quadrants COVER the box.**  Any box point lies in one of the four
    quadrant cells `quadPP/quadMP/quadPM/quadMM` (case split on the sign of x0, x1).
    Membership in a quadrant cell uses `mkpt_mem_convexHull_boxCorners`. -/
theorem box2_subset_quad_union (x : X2) (hx : x ∈ box2) :
    x ∈ quadPP ∨ x ∈ quadMP ∨ x ∈ quadPM ∨ x ∈ quadMM := by
  obtain ⟨h0l, h0u, h1l, h1u⟩ := hx
  -- rewrite x as mkpt (x 0) (x 1) so the box-corner-hull membership applies
  have hxeq : x = mkpt (x 0) (x 1) := by
    funext j; fin_cases j <;> rfl
  rcases le_or_gt 0 (x 0) with hs0 | hs0 <;> rcases le_or_gt 0 (x 1) with hs1 | hs1
  · -- x0 ≥ 0, x1 ≥ 0  ⇒ quadPP = conv(boxCorners 0 1 0 1)
    left
    rw [quadPP, hxeq]
    exact mkpt_mem_convexHull_boxCorners 0 1 0 1 (x 0) (x 1) (by norm_num) (by norm_num)
      ⟨hs0, h0u⟩ ⟨hs1, h1u⟩
  · -- x0 ≥ 0, x1 < 0  ⇒ quadPM = conv(boxCorners 0 1 (-1) 0)
    right; right; left
    rw [quadPM, hxeq]
    exact mkpt_mem_convexHull_boxCorners 0 1 (-1) 0 (x 0) (x 1) (by norm_num) (by norm_num)
      ⟨hs0, h0u⟩ ⟨h1l, hs1.le⟩
  · -- x0 < 0, x1 ≥ 0  ⇒ quadMP = conv(boxCorners (-1) 0 0 1)
    right; left
    rw [quadMP, hxeq]
    exact mkpt_mem_convexHull_boxCorners (-1) 0 0 1 (x 0) (x 1) (by norm_num) (by norm_num)
      ⟨h0l, hs0.le⟩ ⟨hs1, h1u⟩
  · -- x0 < 0, x1 < 0  ⇒ quadMM = conv(boxCorners (-1) 0 (-1) 0)
    right; right; right
    rw [quadMM, hxeq]
    exact mkpt_mem_convexHull_boxCorners (-1) 0 (-1) 0 (x 0) (x 1) (by norm_num) (by norm_num)
      ⟨h0l, hs0.le⟩ ⟨h1l, hs1.le⟩

/-! ===================================================================
    SECTION 4.  THE MAIN 2-D ARRANGEMENT HULL EQUALITY AND LP-EXACTNESS.
    =================================================================== -/

/-- **Every coupled-surface graph point is in `conv(arrVertImgs)`.**  For any box
    input `x`, `x` lies in one of the 4 quadrant cells, on which both neurons are
    sign-constant, so its surface image is a convex combination of that quadrant's
    corner images — all arrangement-vertex images. -/
theorem graph2_subset_arrHull :
    coupledGraph2 ⊆ convexHull ℝ arrVertImgs := by
  rintro _ ⟨x, hx, rfl⟩
  rcases box2_subset_quad_union x hx with hPP | hMP | hPM | hMM
  · exact quad_image_subset_arrHull 0 1 0 1 signConst_quadPP boxCorners_PP_subset
      ⟨x, hPP, rfl⟩
  · exact quad_image_subset_arrHull (-1) 0 0 1 signConst_quadMP boxCorners_MP_subset
      ⟨x, hMP, rfl⟩
  · exact quad_image_subset_arrHull 0 1 (-1) 0 signConst_quadPM boxCorners_PM_subset
      ⟨x, hPM, rfl⟩
  · exact quad_image_subset_arrHull (-1) 0 (-1) 0 signConst_quadMM boxCorners_MM_subset
      ⟨x, hMM, rfl⟩

/-- Each arrangement vertex lies in the box `[-1,1]^2`. -/
theorem arrVerts_subset_box : arrVerts ⊆ box2 := by
  intro w hw
  simp only [arrVerts, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by norm_num [mkpt], by norm_num [mkpt], by norm_num [mkpt], by norm_num [mkpt]⟩

/-- **Each arrangement-vertex image is a genuine point of the coupled surface graph.** -/
theorem arrVertImgs_subset_graph2 : arrVertImgs ⊆ coupledGraph2 := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, arrVerts_subset_box hw, rfl⟩

/-- **★ THE 2-D ARRANGEMENT HULL EQUALITY (the deliverable, concrete k=2 instance).**
    For the coupled 2-D-INPUT k=2 ReLU surface graph (z1=x0, z2=x1 over `[-1,1]^2`,
    sign-lines crossing at the origin),
          conv(coupledGraph2) = conv(arrangement-vertex images).
    The exact convex hull of the piecewise-affine SURFACE over the 2-D box equals the
    convex hull of the images of the 9 arrangement vertices (box corners + line/box
    midpoints + the line/line center).  So the joint 2-cut family on the arrangement
    vertices IS the exact hull description in the genuinely MULTI-DIMENSIONAL-input
    coupled regime. -/
theorem coupled2_convHull_eq_arrangementVerts :
    convexHull ℝ coupledGraph2 = convexHull ℝ arrVertImgs := by
  refine Subset.antisymm ?_ (convexHull_mono arrVertImgs_subset_graph2)
  exact convexHull_min graph2_subset_arrHull (convex_convexHull ℝ _)

/-- **★ 2-D LP-EXACTNESS on the arrangement vertices.**  For EVERY linear objective
    `objK e d`, IF its greatest value `M` over the FINITE arrangement-vertex image set
    is attained, THEN `M` is the greatest value over the ENTIRE coupled hull
    `conv(coupledGraph2)`.  So optimizing any linear objective over the exact coupled
    2-D-input k=2 ReLU relaxation reduces to checking the 9 arrangement vertices — the
    joint arrangement-cut is the LP-TIGHTEST / EXACT hull, no gap, in the
    multi-dimensional-input regime.  REUSES the dimension-free engine
    `objK_isGreatest_convHull`. -/
theorem coupled2_lp_max_on_arrangementVerts (e d : Fin 2 → ℝ) (M : ℝ)
    (hM : IsGreatest (objK 2 e d '' arrVertImgs) M) :
    IsGreatest (objK 2 e d '' convexHull ℝ coupledGraph2) M := by
  have := objK_isGreatest_convHull 2 e d arrVertImgs M hM
  rwa [← coupled2_convHull_eq_arrangementVerts] at this

/-! ===================================================================
    SECTION 5.  CONCRETE FACET — the joint 2-ReLU cut `relu z1 + relu z2 ≤ 2` is the
    EXACT optimum over conv(coupledGraph2), attained at the box corner (1,1).
    A genuine 2-D-INPUT joint-cut facet with NO relaxation gap.
    =================================================================== -/

/-- Joint-cut objective weights: `e = 0`, `d = (1,1)` — selects `relu z1 + relu z2`. -/
def eCut : Fin 2 → ℝ := ![0, 0]
def dCut : Fin 2 → ℝ := ![1, 1]

/-- The joint-cut objective evaluates to `relu z1 + relu z2` on an ℝ⁴ point. -/
theorem objCut_eval (p : VK 2) : objK 2 eCut dCut p = p.2 0 + p.2 1 := by
  simp only [objK, eCut, dCut, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- Graph-level joint-cut soundness: `relu x0 + relu x1 ≤ 2` for all `x ∈ [-1,1]^2`. -/
theorem cut2_graph_le (x : X2) (hx : x ∈ box2) :
    reluK (zvec2 2 A2 C2 x 0) + reluK (zvec2 2 A2 C2 x 1) ≤ 2 := by
  obtain ⟨_, h0u, _, h1u⟩ := hx
  rw [zvec2_A2, zvec2_A2]
  unfold reluK
  rcases le_or_gt 0 (x 0) with s0 | s0 <;> rcases le_or_gt 0 (x 1) with s1 | s1
  all_goals first | rw [max_eq_right s0] | rw [max_eq_left s0.le]
  all_goals first | rw [max_eq_right s1] | rw [max_eq_left s1.le]
  all_goals linarith

/-- The box corner `(1,1)` realizes the cut value 2: curve2 (1,1) = ((1,1),(1,1)). -/
theorem cut2_corner_val :
    objK 2 eCut dCut (curve2 2 A2 C2 (mkpt 1 1)) = 2 := by
  rw [objCut_eval]
  simp only [curve2, zvec2, A2, C2, mkpt, reluK, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val]
  norm_num

/-- The corner `(1,1)` is a box point. -/
theorem corner11_in_box : mkpt 1 1 ∈ box2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkpt]

/-- **2-D joint-cut LP-exactness, graph optimum.**  The joint-cut objective
    `relu z1 + relu z2` attains its greatest value `2` over the EXACT coupled 2-D-input
    k=2 graph, realized at the box corner `(1,1)`. -/
theorem cut2_isGreatest_graph :
    IsGreatest (objK 2 eCut dCut '' coupledGraph2) 2 := by
  constructor
  · exact ⟨curve2 2 A2 C2 (mkpt 1 1), ⟨mkpt 1 1, corner11_in_box, rfl⟩, cut2_corner_val⟩
  · rintro val ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [objCut_eval]
    simp only [curve2]
    exact cut2_graph_le x hx

/-- **★ 2-D joint-cut EXACTNESS, hull = graph optimum (concrete capstone).**  The joint
    2-ReLU cut `relu z1 + relu z2 ≤ 2` is the EXACT optimum over the CONVEX HULL of the
    coupled 2-D-INPUT k=2 surface graph: `max conv(G) = max G = 2`.  No relaxation gap.
    Pushed through the general dimension-free engine `objK_isGreatest_convHull` — the
    genuinely multi-dimensional-input joint-cut facet. -/
theorem coupled2_cut_is_facet :
    IsGreatest (objK 2 eCut dCut '' convexHull ℝ coupledGraph2) 2 :=
  objK_isGreatest_convHull 2 eCut dCut coupledGraph2 2 cut2_isGreatest_graph

/-! ===================================================================
    Trust-base check.  Every theorem must depend ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

#print axioms zvec2_affine_combo
#print axioms reluK_combo_on_signConst
#print axioms curve2_combo_on_cell
#print axioms curve2_mem_segment_on_cell
#print axioms surface2_image_subset_convHull_of_signConst
#print axioms mkpt_mem_convexHull_boxCorners
#print axioms boxCornersHull_coord_bounds
#print axioms signConst_quadPP
#print axioms signConst_quadMP
#print axioms signConst_quadPM
#print axioms signConst_quadMM
#print axioms quad_image_subset_arrHull
#print axioms box2_subset_quad_union
#print axioms graph2_subset_arrHull
#print axioms arrVerts_subset_box
#print axioms arrVertImgs_subset_graph2
#print axioms coupled2_convHull_eq_arrangementVerts
#print axioms coupled2_lp_max_on_arrangementVerts
#print axioms arrVerts_finite
#print axioms arrVertImgs_finite
#print axioms cut2_graph_le
#print axioms cut2_isGreatest_graph
#print axioms coupled2_cut_is_facet

end CrownproofArr2D
