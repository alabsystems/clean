/-
  # coupled_upper_cone_lp_exact — the pattern-facet family IS the exact convex
  # hull of the coupled k-ReLU surface over an n-box, for every upper-cone
  # objective (T-HULL, cover-free, arbitrary k and n)

  Invention-wave-1 PROVE lane.  Sealed conjecture record:
  `data/provenance/invention-wave-1-conjectures-2026-06-11.json`
  (set sha256 00b2f585d355e1b4abc2eb2ab6722dd1375ff65619a905d722da5c7cd4b6e8b4,
  conjecture sha256 565643412c45ef4adf5348c20f5cd94378a474123f7c54f96334cfa7a50fc6cd),
  conjecture "coupled_upper_cone_lp_exact — the pattern-facet family IS the
  exact convex hull of the coupled k-ReLU surface over an n-box, for every
  upper-cone objective (T-HULL, cover-free, arbitrary k and n)".

  ## Statement (as conjectured — proved AS STATED, no weakening)

  For ANY k, ANY n, ANY affine pre-activations `z_i = linVal (p i) x (r i)`
  over ANY box `[xl,xu]`, and any linear objective `e·z + d·a` with `d ≥ 0`
  (the entire upper cone of value-cut directions), the supremum of
  `e·z(x) + d·relu(z(x))` over the coupled graph
  `{(z(x), relu(z(x))) : x ∈ box}` equals the max over the 2^k activation
  patterns `S` of the closed-form affine box-max of the assembled row
  `e + d·1_S`, attained at an explicit box corner — and the same value is the
  exact optimum over the CONVEX HULL of the coupled graph (the facet form).
  No cell cover, no breakpoint enumeration, no dimension restriction.

  * `coupled_upper_cone_lp_exact` — IsGreatest over the coupled value set
    (verbatim sealed statement; supremum-validity AND attainment).
  * `coupled_upper_cone_facet`    — IsGreatest of the linear objective over
    `convexHull ℚ (coupledGraphNK p r xl xu)` at the same pattern-facet max:
    on the upper cone, the pattern-facet family supports the exact hull, so
    no convex relaxation is tighter in any cut direction.
  * `upperCone_patternMax_le_of_valid_bound` — least-valid-bound form: every
    sound upper-cone bound dominates the pattern-facet max (the provable
    stopping rule for cut search: if the family cannot close a leaf, no sound
    value premise in these directions can — the domain genuinely needs a split).

  The mixed-sign cone (`d_i < 0` components, where lower envelopes interact)
  is explicitly NOT claimed, exactly as sealed.

  ## Formalization delta vs the sealed sketch

  Statement-level: NONE in mathematical content.  Cosmetic realizations:
    * The sketch's `boxMaxAffine` is realized by THIS WAVE's already-landed
      `Crownproof.boxMaxAffine` (file `multiReluCutboxexact.lean`, argument
      order `w rr xl xu`, interval-arithmetic closed form
      `rr + ∑_j (w_j·mid_j + |w_j|·rad_j)` — the per-coordinate endpoint max
      of an affine row, O(n) per pattern), imported rather than redefined.
    * The sketch wrote `convexHull ℚ'` (stray quote); we use `convexHull ℚ`.
    * The sketch's facet form wrote the objective inline
      `(fun q => ∑ i, e i * q.1 i + ∑ i, d i * q.2 i)`; it is named
      `upperConeObj` here, and the coupled graph (which had no definition in
      the tree) is defined as `coupledGraphNK` with `q = (z(x), relu∘z(x))`.
    * The main theorem is stated VERBATIM (inline `fun S => boxMaxAffine …`)
      and proved by `coupled_upper_cone_lp_exact_core`, the same statement
      through the abbreviation `upperConePatternBound` (definitionally equal).

  ## Honesty / novelty tier

  N1 AT MOST, "first formalization in this program" — NOT new mathematics.
  Pointwise, `e·z + ∑ d_i·relu z_i = max_S (e·z + ∑_{i∈S} d_i·z_i)` for
  `d ≥ 0` is folklore (kReLU / GCP-CROWN literature); the k=1-over-polytope
  exact hull is Anderson et al. 2020.  The value here is the machine-checked
  general-(k,n) IsGreatest — both over the value set and over the convex hull
  — with an explicit attaining corner and zero geometric cover, lifting this
  tree's instance-only facet results (coupled2/coupled3/coupledTri3/coupled4/
  coupledObl_cut_is_facet) to one theorem, and resolving DEEPCONV_FRONTIER
  §12's stated next target ("what remains open is whether the cut is the
  *exact* hull of the coupled (zonotope) reachable set") for the cut-relevant
  objective cone.  Zero VNN-COMP scored points by itself.

  ## Axioms

  All `#print axioms` below report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axioms
  (verified via `lake build`; see the `#print axioms` commands at the bottom).
-/

import Crownproof.MultiReluCutK
import Crownproof.InventionWave1.multiReluCutboxexact
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull

namespace Crownproof

open Finset

/-! ## 1.  The assembled upper-cone pattern facet

For a pattern `S ⊆ {1..k}` the upper-cone objective `e·z + ∑_{i∈S} d_i·z_i`
is affine in the box input `x`, with row `e·p + ∑_{i∈S} d_i·p_i` and intercept
`e·r + ∑_{i∈S} d_i·r_i`.  Its closed-form box max is one `boxMaxAffine`
evaluation — O(n) per pattern, O(2^k·n) for the whole family. -/

/-- The per-pattern closed-form facet value of the upper-cone objective:
`boxMaxAffine` of the assembled row `e + d·1_S`. -/
def upperConePatternBound {n k : ℕ} (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (S : Finset (Fin k)) : ℚ :=
  boxMaxAffine (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j))
    ((∑ i, e i * r i) + (∑ i ∈ S, d i * r i)) xl xu

/-- Sum of two affine functionals of the box input is affine, rows and
intercepts adding componentwise. -/
theorem linVal_add {n : ℕ} (w₁ w₂ : Fin n → ℚ) (c₁ c₂ : ℚ) (x : Fin n → ℚ) :
    linVal w₁ x c₁ + linVal w₂ x c₂
      = linVal (fun j => w₁ j + w₂ j) x (c₁ + c₂) := by
  unfold linVal
  have hsum : (∑ j, (w₁ j + w₂ j) * x j)
      = (∑ j, w₁ j * x j) + (∑ j, w₂ j * x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- **Pattern assembly for the upper-cone objective.**  Pointwise in `x`,
`e·z(x) + ∑_{i∈S} d_i·z_i(x)` is the affine functional with the assembled row
and intercept of `upperConePatternBound` (two `pattern_affine_assemble` calls
glued by `linVal_add`). -/
theorem upperCone_pattern_assemble {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (x : Fin n → ℚ) (S : Finset (Fin k)) :
    (∑ i, e i * linVal (p i) x (r i)) + (∑ i ∈ S, d i * linVal (p i) x (r i))
      = linVal (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j)) x
          ((∑ i, e i * r i) + (∑ i ∈ S, d i * r i)) := by
  rw [pattern_affine_assemble e p r x Finset.univ,
      pattern_affine_assemble d p r x S, linVal_add]

/-! ## 2.  Upper bound: every coupled value is dominated by the facet max

The active set `A(x) = {i : 0 ≤ z_i(x)}` realizes the ReLU sum as the
`S = A(x)` pattern value (`relu_sum_eq_active_pattern`), the assembled affine
form is interval-bounded by `boxMaxAffine` (`linVal_le_boxMaxAffine`), and
`A(x)` is one of the 2^k patterns in the `sup'`.  No sign condition on `e`,
`d`, and no box-nonemptiness, are needed for this half. -/

/-- **Validity.**  For every `x` in the box, the upper-cone objective value is
dominated by the pattern-facet max — the family is a SOUND family of value
cuts in every upper-cone direction, with an O(2^k·n) closed form. -/
theorem upperConeObj_le_patternMax {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ)
    (x : Fin n → ℚ) (hx : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    (∑ i, e i * linVal (p i) x (r i))
        + (∑ i, d i * relu (linVal (p i) x (r i)))
      ≤ (Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
          (upperConePatternBound e d p r xl xu) := by
  have h1 : (∑ i, d i * relu (linVal (p i) x (r i)))
      = ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ linVal (p i) x (r i)),
          d i * linVal (p i) x (r i) :=
    relu_sum_eq_active_pattern d (fun i => linVal (p i) x (r i))
  rw [h1, upperCone_pattern_assemble e d p r x]
  refine le_trans (linVal_le_boxMaxAffine _ _ xl xu x hx) ?_
  exact Finset.le_sup' (upperConePatternBound e d p r xl xu)
    (Finset.mem_powerset.mpr (Finset.subset_univ _))

/-! ## 3.  The main theorem: EXACTNESS over the coupled value set -/

/-- **Core form** of the sealed statement, through the `upperConePatternBound`
abbreviation (definitionally the sealed `fun S => boxMaxAffine …`).  The
supremum of the upper-cone objective over the coupled graph values is EXACTLY
the pattern-facet max, ATTAINED at the explicit corner `cornerOf w⋆ xl xu` of
the argmax pattern's assembled row `w⋆`.  `hd : d ≥ 0` (the upper cone) is
used ONLY in the attainment half, to dominate every pattern value by the ReLU
sum; the box condition `hbox` only to put the corner in the box. -/
theorem coupled_upper_cone_lp_exact_core {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) (hbox : ∀ j, xl j ≤ xu j) :
    IsGreatest
      {v : ℚ | ∃ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
          v = (∑ i, e i * linVal (p i) x (r i))
              + (∑ i, d i * relu (linVal (p i) x (r i)))}
      ((Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (upperConePatternBound e d p r xl xu)) := by
  constructor
  · -- Membership: the facet max is ATTAINED at the argmax pattern's corner.
    obtain ⟨S, hSmem, hSeq⟩ :=
      Finset.exists_mem_eq_sup'
        (⟨∅, Finset.empty_mem_powerset _⟩ :
          (Finset.univ.powerset (α := Fin k)).Nonempty)
        (upperConePatternBound e d p r xl xu)
    refine ⟨cornerOf (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j)) xl xu,
            cornerOf_mem_box _ xl xu hbox, ?_⟩
    have hle := upperConeObj_le_patternMax e d p r xl xu
      (cornerOf (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j)) xl xu)
      (cornerOf_mem_box _ xl xu hbox)
    rw [hSeq] at hle ⊢
    refine le_antisymm ?_ hle
    -- facet value = linVal w⋆ (corner) = e·z(corner) + ∑_{i∈S} d_i·z_i(corner)
    --             ≤ e·z(corner) + ∑_i d_i·relu (z_i (corner))   [d ≥ 0].
    unfold upperConePatternBound
    rw [← linVal_cornerOf (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j))
          ((∑ i, e i * r i) + (∑ i ∈ S, d i * r i)) xl xu,
        ← upperCone_pattern_assemble e d p r
          (cornerOf (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j)) xl xu) S]
    exact add_le_add le_rfl (weighted_pattern_le_relu_sum d _ hd S)
  · -- Upper bound: every coupled value is dominated by the facet max.
    rintro v ⟨x, hx, rfl⟩
    exact upperConeObj_le_patternMax e d p r xl xu x hx

/-- **`coupled_upper_cone_lp_exact` — the sealed statement, VERBATIM.**
For ANY `k`, ANY `n`, ANY affine pre-activations over ANY box, and ANY
upper-cone objective (`d ≥ 0`), the supremum of `e·z(x) + d·relu(z(x))` over
the coupled graph is EXACTLY the max over the 2^k patterns `S` of the
closed-form affine box-max of the assembled row `e + d·1_S` — `IsGreatest`,
so it is also attained.  Cover-free, breakpoint-free, general position. -/
theorem coupled_upper_cone_lp_exact {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) (hbox : ∀ j, xl j ≤ xu j) :
    IsGreatest
      {v : ℚ | ∃ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
          v = (∑ i, e i * linVal (p i) x (r i))
              + (∑ i, d i * relu (linVal (p i) x (r i)))}
      ((Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (fun S => boxMaxAffine
            (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j))
            ((∑ i, e i * r i) + (∑ i ∈ S, d i * r i)) xl xu)) :=
  coupled_upper_cone_lp_exact_core e d p r xl xu hd hbox

/-! ## 4.  Facet form: the family supports the exact CONVEX HULL

The coupled graph in `(z, a)`-space and the linear upper-cone objective.  A
linear objective's optimum over a convex hull equals its optimum over the
generating set (the sublevel halfspace is convex), so the pattern-facet max is
exactly the hull optimum: on the upper cone, NO convex relaxation of the
coupled reachable set is tighter than the pattern-facet polytope. -/

/-- The coupled k-ReLU graph over the n-box: pre-activation vector paired with
its ReLU image, as the shared input ranges over the box. -/
def coupledGraphNK {n k : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) : Set ((Fin k → ℚ) × (Fin k → ℚ)) :=
  {q | ∃ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
        q = (fun i => linVal (p i) x (r i),
             fun i => relu (linVal (p i) x (r i)))}

/-- The linear objective `e·z + d·a` on the coupled `(z, a)`-space (the
sketch's inline `fun q => ∑ i, e i * q.1 i + ∑ i, d i * q.2 i`, named). -/
def upperConeObj {k : ℕ} (e d : Fin k → ℚ)
    (q : (Fin k → ℚ) × (Fin k → ℚ)) : ℚ :=
  (∑ i, e i * q.1 i) + (∑ i, d i * q.2 i)

/-- The objective's value set over the coupled graph is the coupled value set
of the main theorem. -/
theorem upperConeObj_image_graph {n k : ℕ} (e d : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ) :
    upperConeObj e d '' coupledGraphNK p r xl xu
      = {v : ℚ | ∃ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
          v = (∑ i, e i * linVal (p i) x (r i))
              + (∑ i, d i * relu (linVal (p i) x (r i)))} := by
  ext v
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(fun i => linVal (p i) x (r i),
            fun i => relu (linVal (p i) x (r i))),
           ⟨x, hx, rfl⟩, rfl⟩

/-- Distribute a weighted sum over a two-term convex/linear combination. -/
theorem sum_mul_combo {k : ℕ} (c u v : Fin k → ℚ) (s t : ℚ) :
    (∑ i, c i * (s * u i + t * v i))
      = s * (∑ i, c i * u i) + t * (∑ i, c i * v i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Hull lift.**  `upperConeObj` is linear, so an `IsGreatest` over any set
of coupled points lifts to its convex hull: the sublevel set `{q | obj q ≤ M}`
is convex and contains the generators, hence the hull. -/
theorem upperConeObj_isGreatest_convexHull {k : ℕ} (e d : Fin k → ℚ)
    (G : Set ((Fin k → ℚ) × (Fin k → ℚ))) (M : ℚ)
    (hM : IsGreatest (upperConeObj e d '' G) M) :
    IsGreatest (upperConeObj e d '' convexHull ℚ G) M := by
  obtain ⟨⟨q0, hq0G, hq0v⟩, hub⟩ := hM
  refine ⟨⟨q0, subset_convexHull ℚ G hq0G, hq0v⟩, ?_⟩
  rintro v ⟨q, hq, rfl⟩
  have hhull : convexHull ℚ G ⊆ {w | upperConeObj e d w ≤ M} := by
    apply convexHull_min
    · intro w hw
      exact hub ⟨w, hw, rfl⟩
    · rw [convex_iff_forall_pos]
      rintro a ha b hb s t hs ht hst
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      have hlin : upperConeObj e d (s • a + t • b)
          = s * upperConeObj e d a + t * upperConeObj e d b := by
        simp only [upperConeObj, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
                   Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [sum_mul_combo e a.1 b.1 s t, sum_mul_combo d a.2 b.2 s t]
        ring
      rw [hlin]
      calc s * upperConeObj e d a + t * upperConeObj e d b
          ≤ s * M + t * M :=
            add_le_add (mul_le_mul_of_nonneg_left ha hs.le)
                       (mul_le_mul_of_nonneg_left hb ht.le)
        _ = M := by rw [← add_mul, hst, one_mul]
  exact hhull hq

/-- **`coupled_upper_cone_facet` — the facet form of the sealed statement.**
For every upper-cone direction `(e, d ≥ 0)`, the pattern-facet max is the
EXACT optimum of the linear objective over the CONVEX HULL of the coupled
k-ReLU graph — `IsGreatest`, attained at a graph point.  Hence on the upper
cone the coupled hull is exactly the polytope cut out by the 2^k pattern
facets: there is a supporting pattern facet in every cut direction, and no
convex relaxation of the coupled reachable set is tighter there. -/
theorem coupled_upper_cone_facet {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) (hbox : ∀ j, xl j ≤ xu j) :
    IsGreatest
      (upperConeObj e d '' convexHull ℚ (coupledGraphNK p r xl xu))
      ((Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (fun S => boxMaxAffine
            (fun j => (∑ i, e i * p i j) + (∑ i ∈ S, d i * p i j))
            ((∑ i, e i * r i) + (∑ i ∈ S, d i * r i)) xl xu)) := by
  apply upperConeObj_isGreatest_convexHull
  rw [upperConeObj_image_graph]
  exact coupled_upper_cone_lp_exact e d p r xl xu hd hbox

/-! ## 5.  Verified optimality: the stopping rule for cut search -/

/-- **Least-valid-bound form (per-leaf verified optimality).**  Every bound
`B` sound for the upper-cone objective on the whole box dominates the
pattern-facet max.  With `upperConeObj_le_patternMax` (validity) this is the
provable STOPPING RULE: per leaf box, no sound value premise in any upper-cone
direction is tighter than the pattern-facet family, so a leaf the family
cannot close genuinely requires a split. -/
theorem upperCone_patternMax_le_of_valid_bound {n k : ℕ}
    (e d : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (B : ℚ)
    (hd : ∀ i, 0 ≤ d i) (hbox : ∀ j, xl j ≤ xu j)
    (hvalid : ∀ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        (∑ i, e i * linVal (p i) x (r i))
          + (∑ i, d i * relu (linVal (p i) x (r i))) ≤ B) :
    (Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
      (upperConePatternBound e d p r xl xu) ≤ B := by
  obtain ⟨x, hx, hfx⟩ :=
    (coupled_upper_cone_lp_exact_core e d p r xl xu hd hbox).1
  rw [hfx]
  exact hvalid x hx

/-
  Expected output of every `#print axioms` below (verified via `lake build`):

    'Crownproof.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]

  No `sorryAx`, no domain-specific axioms.
-/
#print axioms linVal_add
#print axioms upperCone_pattern_assemble
#print axioms upperConeObj_le_patternMax
#print axioms coupled_upper_cone_lp_exact_core
#print axioms coupled_upper_cone_lp_exact
#print axioms upperConeObj_image_graph
#print axioms sum_mul_combo
#print axioms upperConeObj_isGreatest_convexHull
#print axioms coupled_upper_cone_facet
#print axioms upperCone_patternMax_le_of_valid_bound

end Crownproof
