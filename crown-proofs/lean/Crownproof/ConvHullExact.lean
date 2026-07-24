/-
  GRAND-CHALLENGE PROGRAM 4 — VERIFIED CONVEX-HULL / LP EXACTNESS for the
  2-ReLU graph over a box.  (Relaxations are OPTIMAL, not merely SOUND.)

  ====================================================================
  WHAT IS PROVEN (sorry-free; trust base = [propext, Classical.choice, Quot.sound])
  ====================================================================

  Fix two ReLU neurons with pre-activations z1 ∈ [l1,u1], z2 ∈ [l2,u2].  Let

      G  =  { (z1, z2, relu z1, relu z2) : z_i ∈ [l_i, u_i] }   ⊂ ℝ⁴

  be the exact 2-ReLU graph over the box, and let `relu z = max 0 z`.

  The CROWN/triangle relaxation describes G by the per-neuron triangle ReLU
  envelopes
        a_i ≥ 0,   a_i ≥ z_i,   a_i ≤ chord_i(z_i)            (triangle_i)
  (the chord = the secant through (l_i,0) and (u_i,u_i)).  The "joint cut family"
  studied in MultiReluCutK / TwoReluCutGeneral adds 2-neuron coupling inequalities.

  THE EXACTNESS THEOREM.  For k = 2 over a *box* (a product domain) the joint cut
  family is REDUNDANT: the per-neuron triangles already cut out the EXACT convex
  hull.  Precisely, we prove

    (HULL, the R⁴ set characterization)
        conv(G)  =  T1 ×ˢ T2,
      where  T_i = conv(G_i)  is exactly the triangle polytope of neuron i
      (Part A: `convHull_eq_triangle`), and the product is the convex hull
      (Part B: `convHull_G_eq_prod`, via mathlib `convexHull_prod`).
      So conv(G) is described by the triangle inequalities ALONE, with NO genuine
      joint facet — every valid joint cut for k=2 over a box is implied.

    (LP-EXACTNESS, the operational optimum form)
        for EVERY linear objective c·z + d·a,
          max over the triangle+cut polytope  =  max over G.
      We prove this with NO relaxation gap: the triangle polytope's optimum over
      any linear objective is attained at a TRUE point of G
      (Part C: `lp_exact`, `triangleSet_lp_attained`), so the relaxed LP and the
      exact combinatorial optimum coincide.  This is the k≤2 exactness the k=3
      demo observed empirically (LP strong duality giving the exact k≤2 optimum),
      here proved as a theorem.

  Honest scope statement (per the task's "ruthlessly honest" instruction):
  for k = 2 over a BOX the convex hull factorizes as a product of the two
  per-neuron triangles — there are NO nontrivial joint facets, so the triangle
  description IS the exact hull and is therefore LP-optimal.  (Genuine joint
  facets only appear when the two pre-activations are coupled through a
  *non-product* feasible z-region, e.g. a shared affine map into a smaller
  polytope; that is the k≥3 / coupled-input regime.)  Everything below is for the
  stated box regime and is proved to the letter.

  We work over ℝ so we can use mathlib's `convexHull`, `segment`, `Convex`,
  `convexHull_prod`.  `reluR z := max 0 z` matches `Crownproof.relu` pointwise.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

namespace Crownproof

open Set

/-- ReLU on the reals (matches `Crownproof.relu : ℚ → ℚ` pointwise). -/
def reluR (z : ℝ) : ℝ := max 0 z

@[simp] theorem reluR_nonneg (z : ℝ) : 0 ≤ reluR z := le_max_left _ _
theorem reluR_ge (z : ℝ) : z ≤ reluR z := le_max_right _ _
theorem reluR_of_nonneg {z : ℝ} (h : 0 ≤ z) : reluR z = z := max_eq_right h
theorem reluR_of_neg {z : ℝ} (h : z ≤ 0) : reluR z = 0 := max_eq_left h

/-! ===================================================================
    SECTION 0.  The triangle polytope of one ReLU neuron.
    =================================================================== -/

/-- The exact graph of one ReLU neuron over `[l,u]`:
    `G_i = { (z, relu z) : l ≤ z ≤ u }`. -/
def neuronGraph (l u : ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ u ∧ p.2 = reluR p.1}

/-- The triangle polytope of one ReLU neuron over the *unstable* box `l < 0 < u`:
    the three ReLU-envelope half-planes intersected with the `z`-box.
    `a ≥ 0`, `a ≥ z`, and the chord  `a ≤ (u/(u-l))·(z - l)` (division-free form
    `a·(u-l) ≤ u·(z-l)`), with `l ≤ z ≤ u`. -/
def triangleSet (l u : ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ u ∧ 0 ≤ p.2 ∧ p.1 ≤ p.2 ∧ p.2 * (u - l) ≤ u * (p.1 - l)}

/-! ===================================================================
    PART A.  conv(G_i) = triangle_i   (each per-neuron triangle is EXACTLY
    the convex hull of the neuron's ReLU graph; no facet missing, none spurious).

    Strategy.  In the unstable case l < 0 < u the graph `G_i` is the union of the
    two ReLU branches; its three extreme points are `(l,0)`, `(0,0)`, `(u,u)`.
    We show

        conv(G_i)  =  conv {(l,0),(0,0),(u,u)}  =  triangleSet l u.

    The middle set is the triangle with those three vertices; `triangleSet` is its
    H-description.  We prove both inclusions of `conv {3 vertices} = triangleSet`
    by hand (V→H trivial by convexity check on vertices; H→V by writing any
    triangle point as an explicit convex combination of the three vertices).
    =================================================================== -/

variable {l u : ℝ}

/-- The three vertices of the unstable ReLU triangle. -/
def triVerts (l u : ℝ) : Set (ℝ × ℝ) := {(l, 0), (0, 0), (u, u)}

/-- `triangleSet` is convex (intersection of half-planes). -/
theorem triangleSet_convex (l u : ℝ) : Convex ℝ (triangleSet l u) := by
  -- Each defining inequality is a convex (affine) constraint; use the explicit
  -- convex-combination characterization.
  rw [convex_iff_forall_pos]
  rintro ⟨x1, a1⟩ ⟨hx1l, hx1u, ha1, hza1, hch1⟩ ⟨x2, a2⟩ ⟨hx2l, hx2u, ha2, hza2, hch2⟩
    s t hs ht hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_add]; nlinarith [hs.le, ht.le]
  · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_add]; nlinarith [hs.le, ht.le]
  · simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_add]; nlinarith [hs.le, ht.le]
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    nlinarith [hs.le, ht.le]
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    -- a-combo · (u-l) ≤ u · (z-combo - l).  Combine hch1, hch2 weighted by s,t.
    -- scaled chords:  s·(a1·(u-l)) ≤ s·(u·(x1-l)),  same for t.
    have e1 : s * (a1 * (u - l)) ≤ s * (u * (x1 - l)) :=
      mul_le_mul_of_nonneg_left hch1 hs.le
    have e2 : t * (a2 * (u - l)) ≤ t * (u * (x2 - l)) :=
      mul_le_mul_of_nonneg_left hch2 ht.le
    -- key identity using s + t = 1 to absorb the intercept:
    have key : s * (u * (x1 - l)) + t * (u * (x2 - l))
             = u * ((s * x1 + t * x2) - l) := by
      have : s * (u * (x1 - l)) + t * (u * (x2 - l))
           = u * (s * x1 + t * x2) - (s + t) * (u * l) := by ring
      rw [this, hst]; ring
    nlinarith [e1, e2, key]

/-- The three vertices lie in `triangleSet` (so does the hull of them). -/
theorem triVerts_subset_triangleSet (hl : l < 0) (hu : 0 < u) :
    triVerts l u ⊆ triangleSet l u := by
  rintro p hp
  simp only [triVerts, mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with h | h | h <;> subst h <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> nlinarith [hl, hu]

/-- The graph `G_i` lies in the triangle (the triangle envelope is SOUND): every
    real ReLU point of the neuron satisfies the three triangle inequalities.
    This is the "(A) soundness of the description" half. -/
theorem neuronGraph_subset_triangleSet (hl : l < 0) (hu : 0 < u) :
    neuronGraph l u ⊆ triangleSet l u := by
  rintro ⟨z, a⟩ ⟨hzl, hzu, ha⟩
  simp only at hzl hzu ha ⊢
  subst ha
  have hul : 0 < u - l := by linarith
  refine ⟨hzl, hzu, reluR_nonneg z, reluR_ge z, ?_⟩
  -- chord soundness: relu z · (u-l) ≤ u · (z - l)
  rcases le_or_gt 0 z with hz | hz
  · rw [reluR_of_nonneg hz]
    -- z·(u-l) ≤ u·(z-l)  ⇔  -z·l ≤ -u·l  ⇔  l·(u - z) ≤ 0  (l<0, u-z≥0)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hl.le (by linarith : (0:ℝ) ≤ u - z)]
  · rw [reluR_of_neg hz.le]
    -- 0 ≤ u·(z-l)  since u>0, z-l ≥ 0
    nlinarith [mul_nonneg hu.le (by linarith : (0:ℝ) ≤ z - l)]

/-- The three vertices lie in the graph `G_i` (extreme points are real ReLU
    points): `(l,0),(0,0),(u,u) ∈ G_i`. -/
theorem triVerts_subset_neuronGraph (hl : l < 0) (hu : 0 < u) :
    triVerts l u ⊆ neuronGraph l u := by
  rintro p hp
  simp only [triVerts, mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with h | h | h <;> subst h
  · exact ⟨le_refl l, hl.le.trans hu.le, (reluR_of_neg hl.le).symm⟩
  · exact ⟨hl.le, hu.le, (reluR_of_neg (le_refl 0)).symm⟩
  · exact ⟨hl.le.trans hu.le, le_refl u, (reluR_of_nonneg hu.le).symm⟩

/-- KEY H→V LEMMA.  Every point of `triangleSet` is a convex combination of the
    three vertices `(l,0), (0,0), (u,u)` — i.e. lies in `conv(triVerts)`.
    This is the crux of EXACTNESS: no point satisfying the triangle inequalities
    escapes the convex hull of the real ReLU graph. -/
theorem triangleSet_subset_convHull_triVerts (hl : l < 0) (hu : 0 < u) :
    triangleSet l u ⊆ convexHull ℝ (triVerts l u) := by
  rintro ⟨z, a⟩ ⟨hzl, hzu, ha0, haz, hch⟩
  simp only at hzl hzu ha0 haz hch
  have hul : (0:ℝ) < u - l := by linarith
  have hnl : (0:ℝ) < -l := by linarith
  -- Barycentric weights of (z,a) w.r.t. vertices (l,0),(0,0),(u,u):
  --   γ = a/u   (from a = γ·u),    α = (a - z)/(-l)   (from z = α·l + γ·u),
  --   β = 1 - α - γ.   We introduce them as plain reals (no `set`) and prove
  --   the three weight facts by clearing denominators.
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ * u = a :=
    ⟨a / u, div_mul_cancel₀ a (ne_of_gt hu)⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α * (-l) = a - z :=
    ⟨(a - z) / (-l), div_mul_cancel₀ (a - z) (ne_of_gt hnl)⟩
  -- nonnegativity of γ and α from the sign data
  have hγ0 : 0 ≤ γ := by nlinarith [hγ, ha0, hu]
  have hα0 : 0 ≤ α := by nlinarith [hα, ha0, haz, hnl]
  -- β := 1 - α - γ ≥ 0  ⇔  α·(-l)·u + γ·u·(-l) ≤ u·(-l), i.e. chord.
  have hβ0 : 0 ≤ 1 - α - γ := by
    -- multiply target (α + γ ≤ 1) by u·(-l) > 0:
    --   α·(-l)·u + γ·u·(-l) ≤ u·(-l)
    --   (a-z)·u + a·(-l) ≤ u·(-l)        [using hα·u, hγ·(-l)]
    --   a·(u-l) - z·u ≤ -u·l  ⇔  a·(u-l) ≤ u·(z-l) = chord.  ✓
    nlinarith [hch, hα, hγ, mul_pos hu hnl, hu, hnl]
  have hsum : α + (1 - α - γ) + γ = 1 := by ring
  -- coordinate reconstruction
  have hzcoord : α * l + (1 - α - γ) * 0 + γ * u = z := by nlinarith [hα, hγ]
  have hacoord : α * 0 + (1 - α - γ) * 0 + γ * u = a := by rw [hγ]; ring
  -- membership of vertices
  have hmemset : (l, (0:ℝ)) ∈ triVerts l u := by simp [triVerts]
  have hmem0 : ((0:ℝ), (0:ℝ)) ∈ triVerts l u := by simp [triVerts]
  have hmemu : (u, u) ∈ triVerts l u := by simp [triVerts]
  have hconv : Convex ℝ (convexHull ℝ (triVerts l u)) := convex_convexHull ℝ _
  -- Assemble the convex combination stepwise:  (z,a) = δ•Q + γ•(u,u),
  -- δ = 1-γ, Q = the (α,β)-combination of (l,0),(0,0).
  by_cases hγ1 : γ = 1
  · -- γ = 1 ⇒ α = β = 0 ⇒ (z,a) = (u,u)
    have hαz : α = 0 := le_antisymm (by linarith [hβ0]) hα0
    have hzeq : z = u := by nlinarith [hzcoord, hαz, hγ1]
    have haeq : a = u := by rw [← hacoord, hαz, hγ1]; ring
    have hpt : (z, a) = (u, u) := by rw [hzeq, haeq]
    rw [hpt]; exact subset_convexHull ℝ _ hmemu
  · have hγle1 : γ ≤ 1 := by linarith [hα0, hβ0]
    have hδpos : 0 < 1 - γ := lt_of_le_of_ne (by linarith) (fun h => hγ1 (by linarith))
    have hδne : (1 - γ) ≠ 0 := ne_of_gt hδpos
    -- rescaled weights for the inner segment {(l,0),(0,0)}
    have hαδ0 : 0 ≤ α / (1 - γ) := div_nonneg hα0 hδpos.le
    have hβδ0 : 0 ≤ (1 - α - γ) / (1 - γ) := div_nonneg hβ0 hδpos.le
    have hαβδ : α / (1 - γ) + (1 - α - γ) / (1 - γ) = 1 := by
      rw [← add_div, div_eq_one_iff_eq hδne]; ring
    set Q : ℝ × ℝ :=
      (α / (1 - γ)) • (l, (0:ℝ)) + ((1 - α - γ) / (1 - γ)) • ((0:ℝ), (0:ℝ)) with hQdef
    have hQmem : Q ∈ convexHull ℝ (triVerts l u) :=
      hconv (subset_convexHull ℝ _ hmemset) (subset_convexHull ℝ _ hmem0)
        hαδ0 hβδ0 hαβδ
    have huu : (u, u) ∈ convexHull ℝ (triVerts l u) := subset_convexHull ℝ _ hmemu
    have hfinal : (z, a) = (1 - γ) • Q + γ • (u, u) := by
      rw [hQdef, smul_add, smul_smul, smul_smul,
          mul_div_cancel₀ α hδne, mul_div_cancel₀ (1 - α - γ) hδne]
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [hzcoord]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linarith [hacoord]
    rw [hfinal]
    exact hconv hQmem huu hδpos.le hγ0 (by ring)

/-- **PART A (the exactness of the per-neuron description).**
    `conv(G_i) = triangleSet l u`.  The triangle ReLU envelope is EXACTLY the
    convex hull of the neuron's ReLU graph — every facet is a triangle inequality
    and every triangle inequality is a facet (no missing valid cut, none spurious). -/
theorem convHull_eq_triangle (hl : l < 0) (hu : 0 < u) :
    convexHull ℝ (neuronGraph l u) = triangleSet l u := by
  apply Subset.antisymm
  · -- conv(G_i) ⊆ triangle :  triangle is convex and contains G_i.
    exact convexHull_min (neuronGraph_subset_triangleSet hl hu) (triangleSet_convex l u)
  · -- triangle ⊆ conv(G_i) :  triangle ⊆ conv(verts) ⊆ conv(G_i).
    calc triangleSet l u
        ⊆ convexHull ℝ (triVerts l u) := triangleSet_subset_convHull_triVerts hl hu
      _ ⊆ convexHull ℝ (neuronGraph l u) :=
            convexHull_mono (triVerts_subset_neuronGraph hl hu)

/-! ===================================================================
    PART B.  conv(G) = T1 ×ˢ T2  (the full R⁴ hull, for k = 2 over a box).

    G factorizes over the product box, so by mathlib's `convexHull_prod`
    its convex hull is the product of the two triangle polytopes.  There is NO
    genuine joint facet: the triangle inequalities of neuron 1 and neuron 2,
    taken together, cut out conv(G) exactly.

    We model the R⁴ graph in coordinates ((z1,a1),(z2,a2)) ∈ (ℝ×ℝ)×(ℝ×ℝ),
    i.e. G = G_1 ×ˢ G_2.
    =================================================================== -/

/-- **PART B (the full convex hull characterization).**  Over a product box,
    `conv(G) = conv(G_1) ×ˢ conv(G_2) = triangleSet_1 ×ˢ triangleSet_2`.
    Hence conv(G) is described by the two per-neuron triangle systems alone —
    the joint-cut family is redundant for k = 2 over a box. -/
theorem convHull_G_eq_prod
    {l1 u1 l2 u2 : ℝ} (hl1 : l1 < 0) (hu1 : 0 < u1) (hl2 : l2 < 0) (hu2 : 0 < u2) :
    convexHull ℝ (neuronGraph l1 u1 ×ˢ neuronGraph l2 u2)
      = triangleSet l1 u1 ×ˢ triangleSet l2 u2 := by
  rw [convexHull_prod, convHull_eq_triangle hl1 hu1, convHull_eq_triangle hl2 hu2]

/-! ===================================================================
    PART C.  LP-EXACTNESS:  max over the (triangle = cut) polytope
             EQUALS max over G, for EVERY linear objective.

    By Part A each per-neuron triangle is conv(G_i); a linear objective over a
    convex hull attains the SAME supremum as over the generating set (the optimum
    is at an extreme point of G_i).  For the SEPARABLE box objective
        f(z1,a1,z2,a2) = c1·z1 + d1·a1 + c2·z2 + d2·a2
    the two neurons decouple, so

        max over (triangle_1 ×ˢ triangle_2)  =  max over (G_1 ×ˢ G_2)  =  max over G.

    We prove the operationally meaningful direction with NO relaxation gap:
    for every linear objective, the relaxed-polytope optimum is ATTAINED at a
    genuine point of G — there is no point of the polytope strictly better than
    the best true ReLU point.  Concretely, the value at ANY polytope point is
    ≤ the max over the 3 vertices of each neuron (= a true G-point), and that
    bound is attained, so the two optima coincide.
    =================================================================== -/

/-- A linear objective on one neuron's plane:  `obj_i(z,a) = c·z + d·a`.
    The maximum of a linear objective over `triangleSet` is attained at one of the
    three vertices (each a real ReLU point in `G_i`).  Hence the relaxed max equals
    the exact max — the per-neuron LP has NO gap. -/
theorem triangle_lp_le_vertexMax (hl : l < 0) (hu : 0 < u) (c d : ℝ)
    {p : ℝ × ℝ} (hp : p ∈ triangleSet l u) :
    c * p.1 + d * p.2
      ≤ max (max (c * l + d * 0) (c * 0 + d * 0)) (c * u + d * u) := by
  -- p ∈ triangle = conv(verts); the objective is linear ⇒ ≤ max over verts.
  -- Expand p as the explicit convex combination from Part A.
  obtain ⟨z, a⟩ := p
  obtain ⟨hzl, hzu, ha0, haz, hch⟩ := hp
  simp only at hzl hzu ha0 haz hch ⊢
  -- Re-derive the barycentric weights exactly as in Part A (no `set`/`field_simp`).
  have hul : (0:ℝ) < u - l := by linarith
  have hnl : (0:ℝ) < -l := by linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ * u = a :=
    ⟨a / u, div_mul_cancel₀ a (ne_of_gt hu)⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α * (-l) = a - z :=
    ⟨(a - z) / (-l), div_mul_cancel₀ (a - z) (ne_of_gt hnl)⟩
  set β : ℝ := 1 - α - γ with hβdef
  have hγ0 : 0 ≤ γ := by nlinarith [hγ, ha0, hu]
  have hα0 : 0 ≤ α := by nlinarith [hα, ha0, haz, hnl]
  have hβ0 : 0 ≤ β := by
    rw [hβdef]; nlinarith [hch, hα, hγ, mul_pos hu hnl, hu, hnl]
  have hsum : α + β + γ = 1 := by rw [hβdef]; ring
  have hzcoord : α * l + β * 0 + γ * u = z := by rw [hβdef]; nlinarith [hα, hγ]
  have hacoord : α * 0 + β * 0 + γ * u = a := by rw [hβdef, hγ]; ring
  -- objective at p equals the convex combination of the objective at the verts.
  have hobj : c * z + d * a
      = α * (c * l + d * 0) + β * (c * 0 + d * 0) + γ * (c * u + d * u) := by
    have hz' : z = α * l + β * 0 + γ * u := hzcoord.symm
    have ha' : a = α * 0 + β * 0 + γ * u := hacoord.symm
    rw [hz', ha']; ring
  -- bound each vertex value by the max, weight nonneg, weights sum to 1.
  set M : ℝ := max (max (c * l + d * 0) (c * 0 + d * 0)) (c * u + d * u) with hM
  have hv1 : c * l + d * 0 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hv2 : c * 0 + d * 0 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hv3 : c * u + d * u ≤ M := le_max_right _ _
  rw [hobj]
  have t1 : α * (c * l + d * 0) ≤ α * M := mul_le_mul_of_nonneg_left hv1 hα0
  have t2 : β * (c * 0 + d * 0) ≤ β * M := mul_le_mul_of_nonneg_left hv2 hβ0
  have t3 : γ * (c * u + d * u) ≤ γ * M := mul_le_mul_of_nonneg_left hv3 hγ0
  have : α * M + β * M + γ * M = M := by
    have : α * M + β * M + γ * M = (α + β + γ) * M := by ring
    rw [this, hsum, one_mul]
  linarith

/-- The per-neuron vertex maximum is ATTAINED at a genuine ReLU point of `G_i`:
    each of the three argmax candidates `(l,0),(0,0),(u,u)` lies in `G_i`, so the
    bound of `triangle_lp_le_vertexMax` is tight — the relaxed optimum is realized
    in `G`. -/
theorem vertexMax_attained_in_neuronGraph (hl : l < 0) (hu : 0 < u) (c d : ℝ) :
    ∃ q ∈ neuronGraph l u,
      c * q.1 + d * q.2
        = max (max (c * l + d * 0) (c * 0 + d * 0)) (c * u + d * u) := by
  have hv1 : (l, (0:ℝ)) ∈ neuronGraph l u :=
    triVerts_subset_neuronGraph hl hu (by simp [triVerts])
  have hv2 : ((0:ℝ), (0:ℝ)) ∈ neuronGraph l u :=
    triVerts_subset_neuronGraph hl hu (by simp [triVerts])
  have hv3 : (u, u) ∈ neuronGraph l u :=
    triVerts_subset_neuronGraph hl hu (by simp [triVerts])
  -- whichever vertex realizes the max
  rcases le_total (max (c * l + d * 0) (c * 0 + d * 0)) (c * u + d * u) with h | h
  · refine ⟨(u, u), hv3, ?_⟩; rw [max_eq_right h]
  · rw [max_eq_left h]
    rcases le_total (c * l + d * 0) (c * 0 + d * 0) with h2 | h2
    · refine ⟨((0:ℝ), (0:ℝ)), hv2, ?_⟩; rw [max_eq_right h2]
    · refine ⟨(l, (0:ℝ)), hv1, ?_⟩; rw [max_eq_left h2]

/-- **PART C (per-neuron LP-EXACTNESS).**  For every linear objective `c·z+d·a`,
    the maximum over the triangle (= cut) polytope EQUALS the maximum over the
    exact ReLU graph `G_i`.  No relaxation gap: the LP optimum is attained at a
    true ReLU point.  Formally: the polytope optimum is a tight upper bound for
    `G_i`-values AND is attained in `G_i`. -/
theorem per_neuron_lp_exact (hl : l < 0) (hu : 0 < u) (c d : ℝ) :
    -- (i) every triangle point's value is ≤ some attained G_i-value (no gap up)
    (∃ q ∈ neuronGraph l u, ∀ p ∈ triangleSet l u,
        c * p.1 + d * p.2 ≤ c * q.1 + d * q.2)
    -- (ii) every G_i point is in the triangle (so its value is a lower witness)
  ∧ neuronGraph l u ⊆ triangleSet l u := by
  obtain ⟨q, hq, hqval⟩ := vertexMax_attained_in_neuronGraph hl hu c d
  refine ⟨⟨q, hq, ?_⟩, neuronGraph_subset_triangleSet hl hu⟩
  intro p hp
  rw [hqval]; exact triangle_lp_le_vertexMax hl hu c d hp

/-- **PART C (joint / k=2 LP-EXACTNESS).**  For the separable box objective
        f = c1·z1 + d1·a1 + c2·z2 + d2·a2
    over the product polytope `triangleSet_1 ×ˢ triangleSet_2`, the maximum equals
    the maximum over the exact 2-ReLU graph `G_1 ×ˢ G_2`.  Concretely, there is a
    genuine point `(q1,q2) ∈ G_1 ×ˢ G_2` whose objective value dominates the
    objective at EVERY point of the relaxed polytope — so the triangle+cut
    relaxation has NO gap and the joint cut family adds nothing for k = 2. -/
theorem joint_lp_exact
    {l1 u1 l2 u2 : ℝ} (hl1 : l1 < 0) (hu1 : 0 < u1) (hl2 : l2 < 0) (hu2 : 0 < u2)
    (c1 d1 c2 d2 : ℝ) :
    ∃ q ∈ neuronGraph l1 u1 ×ˢ neuronGraph l2 u2,
      ∀ p ∈ triangleSet l1 u1 ×ˢ triangleSet l2 u2,
        c1 * p.1.1 + d1 * p.1.2 + c2 * p.2.1 + d2 * p.2.2
          ≤ c1 * q.1.1 + d1 * q.1.2 + c2 * q.2.1 + d2 * q.2.2 := by
  obtain ⟨q1, hq1, hval1⟩ := vertexMax_attained_in_neuronGraph hl1 hu1 c1 d1
  obtain ⟨q2, hq2, hval2⟩ := vertexMax_attained_in_neuronGraph hl2 hu2 c2 d2
  refine ⟨(q1, q2), ⟨hq1, hq2⟩, ?_⟩
  rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
  -- per-neuron bounds: each polytope point's value ≤ the vertex-max = q-value.
  have h1 := triangle_lp_le_vertexMax hl1 hu1 c1 d1 hp1
  have h2 := triangle_lp_le_vertexMax hl2 hu2 c2 d2 hp2
  -- rewrite the vertex-maxima as the genuine q-values (goal direction).
  rw [← hval1] at h1
  rw [← hval2] at h2
  -- objective separates; sum the two per-neuron bounds.
  simp only [Prod.fst, Prod.snd] at h1 h2 ⊢
  linarith

/-! ===================================================================
    PART D.  The capstone EQUALITY of optima (the LP-exactness in
    "max = max" form, as an `IsGreatest`).

    Define the objective-value images
        valsPoly = { f(p) : p ∈ triangle_1 ×ˢ triangle_2 }   (relaxation)
        valsG    = { f(p) : p ∈ G_1 ×ˢ G_2 }                 (exact graph)
    where f is the separable linear objective.  We exhibit a common greatest
    element M of BOTH sets: M is achieved at a real ReLU point of G (so M ∈ valsG
    and M ∈ valsPoly since G ⊆ polytope), and M dominates every polytope value
    (so it is the greatest of valsPoly, a fortiori of the smaller valsG).
    Therefore  max valsPoly = max valsG = M : the relaxed LP optimum EQUALS the
    exact optimum, with NO gap.
    =================================================================== -/

/-- The separable linear objective on the R⁴ point `((z1,a1),(z2,a2))`. -/
def jointObj (c1 d1 c2 d2 : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  c1 * p.1.1 + d1 * p.1.2 + c2 * p.2.1 + d2 * p.2.2

/-- **PART D (LP-exactness as an equality of maxima).**  There is a single value
    `M` that is simultaneously the maximum of the linear objective over the
    *relaxed* triangle+cut polytope AND over the *exact* 2-ReLU graph `G`.  Hence

        max over (triangle_1 ×ˢ triangle_2) (jointObj) = M = max over G (jointObj),

    i.e. the relaxation has NO optimality gap for k = 2 over a box. -/
theorem joint_lp_max_eq
    {l1 u1 l2 u2 : ℝ} (hl1 : l1 < 0) (hu1 : 0 < u1) (hl2 : l2 < 0) (hu2 : 0 < u2)
    (c1 d1 c2 d2 : ℝ) :
    ∃ M : ℝ,
      IsGreatest (jointObj c1 d1 c2 d2 '' (triangleSet l1 u1 ×ˢ triangleSet l2 u2)) M
    ∧ IsGreatest (jointObj c1 d1 c2 d2 '' (neuronGraph l1 u1 ×ˢ neuronGraph l2 u2)) M := by
  obtain ⟨q, hqmem, hqdom⟩ := joint_lp_exact hl1 hu1 hl2 hu2 c1 d1 c2 d2
  -- G ⊆ polytope (soundness of the triangle description on the product box)
  have hGsub : neuronGraph l1 u1 ×ˢ neuronGraph l2 u2
             ⊆ triangleSet l1 u1 ×ˢ triangleSet l2 u2 := by
    rintro ⟨r1, r2⟩ ⟨hr1, hr2⟩
    exact ⟨neuronGraph_subset_triangleSet hl1 hu1 hr1,
           neuronGraph_subset_triangleSet hl2 hu2 hr2⟩
  refine ⟨jointObj c1 d1 c2 d2 q, ⟨⟨q, hGsub hqmem, rfl⟩, ?_⟩, ⟨q, hqmem, rfl⟩, ?_⟩
  · -- M is an upper bound of the relaxed-polytope value set
    rintro v ⟨p, hp, rfl⟩; exact hqdom p hp
  · -- M is an upper bound of the exact-graph value set (a fortiori, G ⊆ polytope)
    rintro v ⟨p, hp, rfl⟩; exact hqdom p (hGsub hp)

/-! ===================================================================
    Trust-base check.  Every theorem must depend ONLY on
    [propext, Classical.choice, Quot.sound] — NO sorryAx.
    =================================================================== -/

#print axioms convHull_eq_triangle
#print axioms convHull_G_eq_prod
#print axioms triangleSet_convex
#print axioms triangleSet_subset_convHull_triVerts
#print axioms neuronGraph_subset_triangleSet
#print axioms triangle_lp_le_vertexMax
#print axioms vertexMax_attained_in_neuronGraph
#print axioms per_neuron_lp_exact
#print axioms joint_lp_exact
#print axioms joint_lp_max_eq

end Crownproof
