/-
  INVENTION WAVE 1 — `deep_cut_propagation`

  Sealed conjecture: "deep_cut_propagation — layer-2 cuts derived over the
  layer-1 cut polytope are sound and dominate the §8 zU-substitution
  construction; facet propagation retains the coupling that CROWN substitution
  provably spends."
  Provenance: data/provenance/invention-wave-1-conjectures-2026-06-11.json,
  angle `tighter-relaxations`, conjecture sha256
  244a4e4d635beb604ec274108be29926ef91b85d6f1d28a26670485b0969651d
  (sealed 2026-06-11 BEFORE any proof attempt).

  ## RESULT STATUS — proved-weakened (documented delta), sorry-free

  PROVED AS CONJECTURED (the two theorem legs of the sealed statement):
   1. `deep_cut_propagation_sound` — any B₂ dominating the layer-2 readout
      objective over the layer-1 cut polytope P_cut is a SOUND joint deep-cut
      bound on every genuine execution, because the genuine point
      (x, z¹(x), relu (z¹(x))) lies in P_cut (`genuine_in_cut_polytope`).
   2. `deep_cut_dominates_triangle` — P_cut ⊆ P_tri (`cutFeasible_triFeasible`),
      hence every bound valid over the triangle-only polytope is valid over
      P_cut: the optimal P_cut bound is ≤ the optimal P_tri bound (dominance,
      stated in valid-bound form — no sup machinery needed).
   3. `facet_bound_of_corners` — the pattern-facet bounds of P_cut are
      DERIVABLE from finitely many box-corner inequalities (the V-description /
      computability leg), by reduction to `multiReluCut_box_le` with indicator
      weights.

  STRICT INSTANCE — landed as the SYNTHETIC fallback the sealed conjecture
  itself names ("Fallback: a synthetic 2-layer instance … still proves the
  mechanism"):
   4. `deep_cut_strict_instance` — on the sealed k = 3 coupling demo of
      `MultiReluCutK.lean` (z₁ = x₁, z₂ = −x₁+2x₂, z₃ = −x₁−2x₂ on [−1,1]²)
      feeding a single layer-2 readout z² = a₁+a₂+a₃ with dd = 1:
        * the PROPAGATED bound B₂(P_cut) = 3 is valid (`dcp_B2cut_valid`) and
          attained by a genuine execution (`dcp_B2cut_floor`), so it is EXACT;
        * the §8 zU-substitution construction (per-neuron CROWN upper chords
          substituted into the layer-2 readout, then maximised over the box)
          yields EXACTLY 4: sound (`dcp_zU_le_four`) and attained at a box
          point (`dcp_zU_floor`);
        * 3 < 4 — facet propagation is STRICTLY tighter than zU substitution.
   5. `deep_cut_strict_vs_triangle` — stronger: NO bound valid over the
      triangle-only polytope can be below 7/2 (`dcp_tri_floor`, explicit
      relaxation witness), so the propagated bound 3 strictly beats the BEST
      possible triangle-only LP bound, not just the zU construction: 3 < 7/2.
   6. `deepCut_as_farkas_premise` — the propagated layer-2 cut enters the
      kernel-checked `farkas_premise_combination` as one ≥0-multiplier premise:
      the cut composition law ACROSS layers (layer-1 facets become a layer-2
      premise) bottoms out in the same Farkas core as every other Crownproof
      bound.

  NOT PROVED HERE (honest scope, per the sealed risk notes):
   * The strict instance at a REAL deep pair (e.g. ACAS L2 (36,46)) is NOT
     attempted: the real leaf input is 5-D and P_cut vertex enumeration there
     needs the cell-cover machinery the program docs call combinatorially
     heavy.  The synthetic instance proves the MECHANISM only.
   * No claim that propagation dominates the literal §8 zU bound on ALL
     geometries (the sealed risk note (b) explicitly disclaims this); the
     general theorem is dominance vs P_tri, the zU comparison is per-instance.
   * No Δdomains / wall-clock / VNN-COMP claims; the deep Δdomains payoff is
     unmeasured until the sibling §3C protocol runs.

  ## FORMALIZATION DELTA vs the sealed Lean sketch (minimal, documented)

   * The sketch's `patternBound (fun _ => 1) p r xl xu S` does not exist in the
     substrate (Conjecture 1 has not landed).  The facet bounds are therefore
     carried as an abstract family `BS : Finset (Fin k) → ℚ` inside
     `CutFeasible`, with validity (`FacetFamilyValid`) a hypothesis of the
     soundness theorem, and `facet_bound_of_corners` providing the constructive
     corner-max instantiation (what `patternBound` would compute).
   * `CutFeasible` is packaged as `TriFeasible ∧ facets` (sketch wrote it
     flat); propositionally identical, makes P_cut ⊆ P_tri one projection.
   * The triangle upper envelope is stated division-free,
     `a·(u−l) ≤ u·(z−l)`, matching `Basic.relu_upper`'s exact-rational style.
   * The sketch's elided `hlz/huz` hypotheses are spelled out: sound
     pre-activation bounds over the box plus WEAK unstability
     `lz ≤ 0 ≤ uz` (weak suffices for the genuine point to satisfy the chord).
   * `hdd : ∀ i, 0 ≤ dd i` is DROPPED from `deep_cut_propagation_sound`: the
     soundness of a P_cut-valid bound at genuine executions needs no sign
     condition on dd (the genuine point is feasible regardless).  dd ≥ 0
     matters only when the cut is consumed as a Farkas premise downstream
     (and `deepCut_as_farkas_premise` needs only μ₀ ≥ 0 for that).

  ## Honesty rails (novelty-tier standard, designs/2026-06-11 addendum)

  N1 at most.  GCP-CROWN (Zhang et al.) propagates general cutting planes
  numerically — the delta here is the machine-checked derivation chain
  (facet validity → polytope membership → propagated bound soundness →
  Farkas composition) with exact rationals, NOT a new bound-propagation idea.
  "First formalization" claims require the literature leg; nothing here is
  "new mathematics."

  All `#print axioms` must report `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx` — verified in the build log (the `#print axioms` commands at
  the bottom of this file emit it).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Crownproof.MultiReluCutK
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Crownproof

open Finset

/-! ## 1.  The layer-1 polytopes.

`TriFeasible` is the verified triangle-only relaxation over the leaf box:
box membership, affine pre-activations `z_i = linVal (p i) x (r i)`, and the
three ReLU triangle inequalities per neuron (lower envelopes `a ≥ 0`, `a ≥ z`
and the division-free upper chord `a·(uz−lz) ≤ uz·(z−lz)`).

`CutFeasible` is `TriFeasible` PLUS the pattern facets: for every activation
pattern `S ⊆ [k]`, `∑_{i∈S} a_i ≤ BS S`.  The facet bounds are carried as an
abstract family `BS`; their validity is the `FacetFamilyValid` hypothesis
below, and `facet_bound_of_corners` shows how to DERIVE a valid family from
finitely many box-corner inequalities. -/

/-- The triangle-only relaxation polytope `P_tri` (membership predicate). -/
def TriFeasible {n k : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (lz uz : Fin k → ℚ)
    (x : Fin n → ℚ) (z a : Fin k → ℚ) : Prop :=
  (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
  (∀ i, z i = linVal (p i) x (r i)) ∧
  (∀ i, 0 ≤ a i ∧ z i ≤ a i ∧ a i * (uz i - lz i) ≤ uz i * (z i - lz i))

/-- The layer-1 cut polytope `P_cut` (membership predicate): triangles PLUS
the pattern facets `∑_{i∈S} a_i ≤ BS S` for every pattern `S`. -/
def CutFeasible {n k : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (lz uz : Fin k → ℚ) (BS : Finset (Fin k) → ℚ)
    (x : Fin n → ℚ) (z a : Fin k → ℚ) : Prop :=
  TriFeasible p r xl xu lz uz x z a ∧
  (∀ S : Finset (Fin k), (∑ i ∈ S, a i) ≤ BS S)

/-- Validity of a pattern-facet family: each `BS S` dominates the genuine
sub-group ReLU sum `∑_{i∈S} relu (z_i(x))` over the whole box. -/
def FacetFamilyValid {n k : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (BS : Finset (Fin k) → ℚ) : Prop :=
  ∀ (S : Finset (Fin k)) (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
    (∑ i ∈ S, relu (linVal (p i) x (r i))) ≤ BS S

/-! ## 2.  The genuine execution point lies in `P_cut`. -/

/-- Division-free ReLU upper chord soundness on a weakly-unstable interval:
for `l ≤ 0 ≤ u` and `l ≤ z ≤ u`, `relu z · (u − l) ≤ u · (z − l)`.
(The division-free form of `Basic.relu_upper`; weak unstability suffices.) -/
theorem dcp_relu_chord_sound (l u z : ℚ) (hl0 : l ≤ 0) (hu0 : 0 ≤ u)
    (hzl : l ≤ z) (hzu : z ≤ u) :
    relu z * (u - l) ≤ u * (z - l) := by
  unfold relu
  rcases le_or_gt 0 z with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hl0 (by linarith : (0:ℚ) ≤ u - z)]
  · rw [max_eq_left (le_of_lt h), zero_mul]
    exact mul_nonneg hu0 (by linarith)

/-- **The genuine execution is `P_cut`-feasible.**  For any box point `x`, the
point `(x, z¹(x), relu (z¹(x)))` satisfies every `CutFeasible` conjunct: box
trivially, affinity by definition, triangles by ReLU envelope soundness, and
the pattern facets by `FacetFamilyValid`. -/
theorem genuine_in_cut_polytope {n k : ℕ}
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (lz uz : Fin k → ℚ) (BS : Finset (Fin k) → ℚ)
    (hlz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        lz i ≤ linVal (p i) x (r i))
    (huz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        linVal (p i) x (r i) ≤ uz i)
    (hunst : ∀ i, lz i ≤ 0 ∧ 0 ≤ uz i)
    (hBS : FacetFamilyValid p r xl xu BS)
    (x : Fin n → ℚ) (hbox : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    CutFeasible p r xl xu lz uz BS x
      (fun i => linVal (p i) x (r i)) (fun i => relu (linVal (p i) x (r i))) := by
  unfold CutFeasible TriFeasible
  refine ⟨⟨hbox, fun i => rfl, fun i => ⟨?_, ?_, ?_⟩⟩, fun S => ?_⟩
  · show (0:ℚ) ≤ relu (linVal (p i) x (r i))
    unfold relu; exact le_max_left _ _
  · show linVal (p i) x (r i) ≤ relu (linVal (p i) x (r i))
    unfold relu; exact le_max_right _ _
  · show relu (linVal (p i) x (r i)) * (uz i - lz i)
        ≤ uz i * (linVal (p i) x (r i) - lz i)
    exact dcp_relu_chord_sound (lz i) (uz i) _ (hunst i).1 (hunst i).2
      (hlz i x hbox) (huz i x hbox)
  · show (∑ i ∈ S, relu (linVal (p i) x (r i))) ≤ BS S
    exact hBS S x hbox

/-! ## 3.  Soundness of the propagated deep cut (theorem leg 1). -/

/-- **`deep_cut_propagation_sound`.**  Fix layer-2 readouts
`z²_i = ∑_t v_{it}·a¹_t + b2_i` and weights `dd`.  Any `B2` dominating the
layer-2 objective `∑_i dd_i · relu (z²_i)` over the layer-1 cut polytope
`P_cut` is a SOUND joint deep-cut bound on every genuine execution: for every
box input `x`, the genuine value
`∑_i dd_i · relu (∑_t v_{it} · relu (z¹_t(x)) + b2_i) ≤ B2`.

(No sign condition on `dd` is needed — the genuine point is `P_cut`-feasible
regardless; `dd ≥ 0` matters only for the downstream Farkas use.) -/
theorem deep_cut_propagation_sound {n k m : ℕ}
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (lz uz : Fin k → ℚ) (BS : Finset (Fin k) → ℚ)
    (hlz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        lz i ≤ linVal (p i) x (r i))
    (huz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        linVal (p i) x (r i) ≤ uz i)
    (hunst : ∀ i, lz i ≤ 0 ∧ 0 ≤ uz i)
    (hBS : FacetFamilyValid p r xl xu BS)
    (v : Fin m → Fin k → ℚ) (b2 dd : Fin m → ℚ) (B2 : ℚ)
    (hB2 : ∀ (x : Fin n → ℚ) (z a : Fin k → ℚ),
        CutFeasible p r xl xu lz uz BS x z a →
        (∑ i, dd i * relu ((∑ t, v i t * a t) + b2 i)) ≤ B2) :
    ∀ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
      (∑ i, dd i * relu ((∑ t, v i t * relu (linVal (p t) x (r t))) + b2 i))
        ≤ B2 :=
  fun x hbox =>
    hB2 x (fun i => linVal (p i) x (r i)) (fun i => relu (linVal (p i) x (r i)))
      (genuine_in_cut_polytope p r xl xu lz uz BS hlz huz hunst hBS x hbox)

/-! ## 4.  Dominance over the triangle-only polytope (theorem leg 2). -/

/-- `P_cut ⊆ P_tri`: dropping the facet conjunct. -/
theorem cutFeasible_triFeasible {n k : ℕ}
    {p : Fin k → Fin n → ℚ} {r : Fin k → ℚ} {xl xu : Fin n → ℚ}
    {lz uz : Fin k → ℚ} {BS : Finset (Fin k) → ℚ}
    {x : Fin n → ℚ} {z a : Fin k → ℚ}
    (h : CutFeasible p r xl xu lz uz BS x z a) :
    TriFeasible p r xl xu lz uz x z a :=
  h.1

/-- **`deep_cut_dominates_triangle`.**  Since `P_cut ⊆ P_tri`, every bound on
ANY objective `f` valid over the triangle-only polytope is valid over the cut
polytope.  In particular the optimal (least valid) `B2` over `P_cut` is `≤`
the optimal `B2` over `P_tri` — the propagated relaxation never loses to the
triangle-only relaxation.  (Dominance in valid-bound form; no `sup` machinery
is needed, and the statement is exactly what the BaB consumer uses.) -/
theorem deep_cut_dominates_triangle {n k : ℕ}
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (lz uz : Fin k → ℚ) (BS : Finset (Fin k) → ℚ)
    (f : (Fin n → ℚ) → (Fin k → ℚ) → (Fin k → ℚ) → ℚ) (B : ℚ)
    (hB : ∀ x z a, TriFeasible p r xl xu lz uz x z a → f x z a ≤ B) :
    ∀ x z a, CutFeasible p r xl xu lz uz BS x z a → f x z a ≤ B :=
  fun x z a h => hB x z a (cutFeasible_triFeasible h)

/-! ## 5.  Deriving the facet family from box corners (computability leg).

The facet bounds of `P_cut` are not assumed: for each pattern `S`, a bound `B`
dominating the per-subpattern affine forms `∑_{i∈T} z_i` (`T ⊆ S`) at every
box corner is a valid facet bound.  This is `multiReluCut_box_le` with
indicator weights — the finite corner enumeration the existing V-description
theorems make effective. -/

/-- **`facet_bound_of_corners`.**  If `B` dominates
`linVal (∑_{i∈T} p_i) y (∑_{i∈T} r_i)` for every subpattern `T ⊆ S` and every
box corner `y`, then `∑_{i∈S} relu (z_i(x)) ≤ B` on the whole box — i.e. `B`
is a valid pattern-facet bound for `S`. -/
theorem facet_bound_of_corners {n k : ℕ}
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (S : Finset (Fin k)) (B : ℚ)
    (hcorn : ∀ T : Finset (Fin k), T ⊆ S →
        ∀ y : Fin n → ℚ, (∀ j, y j = xl j ∨ y j = xu j) →
        linVal (fun j => ∑ i ∈ T, p i j) y (∑ i ∈ T, r i) ≤ B) :
    ∀ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
      (∑ i ∈ S, relu (linVal (p i) x (r i))) ≤ B := by
  intro x hbox
  classical
  have hcc : ∀ i, (0:ℚ) ≤ if i ∈ S then (1:ℚ) else 0 := by
    intro i; by_cases h : i ∈ S <;> simp [h]
  have hcornInd : ∀ (T : Finset (Fin k)) (y : Fin n → ℚ),
      (∀ j, y j = xl j ∨ y j = xu j) →
      linVal (fun j => ∑ i ∈ T, (if i ∈ S then (1:ℚ) else 0) * p i j) y
        (∑ i ∈ T, (if i ∈ S then (1:ℚ) else 0) * r i) ≤ B := by
    intro T y hy
    have hw : (fun j => ∑ i ∈ T, (if i ∈ S then (1:ℚ) else 0) * p i j)
        = fun j => ∑ i ∈ T ∩ S, p i j := by
      funext j
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem]
    have hr : (∑ i ∈ T, (if i ∈ S then (1:ℚ) else 0) * r i)
        = ∑ i ∈ T ∩ S, r i := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem]
    rw [hw, hr]
    exact hcorn (T ∩ S) Finset.inter_subset_right y hy
  have hsum : (∑ i, (if i ∈ S then (1:ℚ) else 0) * relu (linVal (p i) x (r i)))
      = ∑ i ∈ S, relu (linVal (p i) x (r i)) := by
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_mem]
  calc (∑ i ∈ S, relu (linVal (p i) x (r i)))
      = ∑ i, (if i ∈ S then (1:ℚ) else 0) * relu (linVal (p i) x (r i)) :=
        hsum.symm
    _ ≤ B := multiReluCut_box_le (fun i => if i ∈ S then (1:ℚ) else 0)
        p r xl xu B hcc x hbox hcornInd

/-! ## 6.  Farkas composition: the propagated cut as one ≥0-multiplier premise.

The cut composition law across layers: the layer-1 facets become a single
layer-2 premise `obj(a) − B2 ≤ 0`, consumed by the SAME kernel-checked
`farkas_premise_combination` every other Crownproof bound bottoms out in. -/

/-- A two-layer relaxed-network state: leaf input, layer-1 pre/post
activations, and the scalar output. -/
structure DeepCutState (n k : ℕ) where
  x : Fin n → ℚ
  z : Fin k → ℚ
  a : Fin k → ℚ
  out : ℚ

/-- Genuine two-layer execution: box input, affine layer-1 pre-activations,
exact ReLUs, and `out = const − ∑_i dd_i · relu (∑_t v_{it}·a_t + b2_i)`. -/
def DeepCutState.valid {n k m : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (v : Fin m → Fin k → ℚ) (b2 dd : Fin m → ℚ)
    (const : ℚ) (st : DeepCutState n k) : Prop :=
  (∀ j, xl j ≤ st.x j ∧ st.x j ≤ xu j) ∧
  (∀ i, st.z i = linVal (p i) st.x (r i)) ∧
  (∀ i, st.a i = relu (st.z i)) ∧
  st.out = const - (∑ i, dd i * relu ((∑ t, v i t * st.a t) + b2 i))

/-- **`deepCut_as_farkas_premise`.**  The propagated deep cut
`(∑_i dd_i · relu (z²_i)) − B2 ≤ 0` is a sound `≥0`-multiplier premise of the
abstract Farkas core: given a `P_cut`-valid `B2` (`hB2`), a multiplier
`μ₀ ≥ 0`, and the certificate identity `μ₀·(obj − B2) = −out − c` as a
function of the state, every genuine execution has `out ≥ −c`.  Reduction to
`farkas_premise_combination`. -/
theorem deepCut_as_farkas_premise {n k m : ℕ}
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (lz uz : Fin k → ℚ) (BS : Finset (Fin k) → ℚ)
    (hlz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        lz i ≤ linVal (p i) x (r i))
    (huz : ∀ i (x : Fin n → ℚ), (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        linVal (p i) x (r i) ≤ uz i)
    (hunst : ∀ i, lz i ≤ 0 ∧ 0 ≤ uz i)
    (hBS : FacetFamilyValid p r xl xu BS)
    (v : Fin m → Fin k → ℚ) (b2 dd : Fin m → ℚ)
    (const B2 c μ0 : ℚ) (hμ0 : 0 ≤ μ0)
    (hB2 : ∀ (x : Fin n → ℚ) (z a : Fin k → ℚ),
        CutFeasible p r xl xu lz uz BS x z a →
        (∑ i, dd i * relu ((∑ t, v i t * a t) + b2 i)) ≤ B2)
    (hcert : ∀ st : DeepCutState n k,
        μ0 * ((∑ i, dd i * relu ((∑ t, v i t * st.a t) + b2 i)) - B2)
          = -(st.out) - c) :
    ∀ st : DeepCutState n k,
      DeepCutState.valid p r xl xu v b2 dd const st → -c ≤ st.out := by
  refine farkas_premise_combination (S := DeepCutState n k) (ι := Fin 1)
    (premises := Finset.univ)
    (g := fun _ st => (∑ i, dd i * relu ((∑ t, v i t * st.a t) + b2 i)) - B2)
    (out := fun st => st.out)
    (μ := fun _ => μ0) (c := c)
    (valid := DeepCutState.valid p r xl xu v b2 dd const)
    ?hμ ?hg ?hcert
  case hμ => intro i _; exact hμ0
  case hg =>
    intro _ _ st hv
    simp only []
    have hgen := deep_cut_propagation_sound p r xl xu lz uz BS hlz huz hunst hBS
      v b2 dd B2 hB2 st.x hv.1
    have heq : (∑ i, dd i * relu ((∑ t, v i t * st.a t) + b2 i))
        = (∑ i, dd i * relu
            ((∑ t, v i t * relu (linVal (p t) st.x (r t))) + b2 i)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hin : (∑ t, v i t * st.a t)
          = (∑ t, v i t * relu (linVal (p t) st.x (r t))) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hv.2.2.1 t, hv.2.1 t]
      rw [hin]
    rw [heq]
    linarith
  case hcert =>
    intro st
    simp only [Fin.sum_univ_one]
    exact hcert st

/-! ## 7.  The STRICT instance (synthetic mechanism demo — the sealed
fallback; the real-pair instance remains open, see header).

We reuse the sealed k = 3 genuine-3-way-coupling demo of `MultiReluCutK.lean`
verbatim: box `[−1,1]²`, `z₁ = x₁`, `z₂ = −x₁+2x₂`, `z₃ = −x₁−2x₂`
(`demoP`/`demoR`/`demoXl`/`demoXu`), and feed layer 2 with the single readout
`z² = a₁ + a₂ + a₃` (v = 1, b2 = 0) and weight `dd = 1`.

  * Pre-activation bounds: `lz = (−1,−3,−3)`, `uz = (1,3,3)` — sound over the
    box and weakly unstable.
  * Facet family: `BS S = 3` for every `S` — valid because the joint 3-cut
    `∑ relu z_i ≤ 3` is the DERIVED bound `demo_joint_cut_le`.
  * Propagated bound: `B₂(P_cut) = 3`, valid AND attained (genuine point
    `x* = (−1,1)` has objective exactly 3) — exact.
  * §8 zU-substitution: per-neuron upper chords (all slope 1/2) substituted
    into the readout give `zU(x) = (7 − x₁)/2`, box max `4`, attained at
    `x = (−1,0)` — the construction's value is exactly 4.
  * Triangle-only floor: the explicit `P_tri` point `x = (0,−1)`,
    `a = (1/2,1/2,5/2)` has objective `7/2`, so NO triangle-only bound is
    below `7/2`.

  Strict chain:  3 = B₂(P_cut)  <  7/2 ≤ B₂(P_tri)  ≤(here)  4 = B₂(zU). -/

/-- Demo layer-1 pre-activation lower bounds. -/
def dcpLz : Fin 3 → ℚ
  | 0 => -1
  | 1 => -3
  | 2 => -3

/-- Demo layer-1 pre-activation upper bounds. -/
def dcpUz : Fin 3 → ℚ
  | 0 => 1
  | 1 => 3
  | 2 => 3

/-- Demo facet family: the derived joint 3-cut bound `3` for every pattern. -/
def dcpBS : Finset (Fin 3) → ℚ := fun _ => 3

/-- Demo layer-2 weights (single readout `z² = a₁ + a₂ + a₃`). -/
def dcpV : Fin 1 → Fin 3 → ℚ := fun _ _ => 1

/-- Demo layer-2 bias (zero). -/
def dcpB2 : Fin 1 → ℚ := fun _ => 0

/-- Demo objective weights (`dd = 1`). -/
def dcpDD : Fin 1 → ℚ := fun _ => 1

/-- The demo pre-activation lower bounds are sound over the box. -/
theorem dcp_lz_sound : ∀ i (x : Fin 2 → ℚ),
    (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
    dcpLz i ≤ linVal (demoP i) x (demoR i) := by
  intro i x hbox
  obtain ⟨h0l, h0u⟩ := hbox 0
  obtain ⟨h1l, h1u⟩ := hbox 1
  simp only [demoXl, demoXu] at h0l h0u h1l h1u
  fin_cases i <;>
  · simp only [dcpLz, demoP, demoR, linVal, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    linarith

/-- The demo pre-activation upper bounds are sound over the box. -/
theorem dcp_uz_sound : ∀ i (x : Fin 2 → ℚ),
    (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
    linVal (demoP i) x (demoR i) ≤ dcpUz i := by
  intro i x hbox
  obtain ⟨h0l, h0u⟩ := hbox 0
  obtain ⟨h1l, h1u⟩ := hbox 1
  simp only [demoXl, demoXu] at h0l h0u h1l h1u
  fin_cases i <;>
  · simp only [dcpUz, demoP, demoR, linVal, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    linarith

/-- The demo bounds are (weakly) unstable: `lz ≤ 0 ≤ uz`. -/
theorem dcp_unstable : ∀ i : Fin 3, dcpLz i ≤ 0 ∧ 0 ≤ dcpUz i := by
  intro i
  fin_cases i <;> exact ⟨by norm_num [dcpLz], by norm_num [dcpUz]⟩

/-- The constant facet family `BS S = 3` is VALID: every sub-group ReLU sum is
dominated by the full joint 3-cut, which `demo_joint_cut_le` DERIVES from box
corners.  (This is the propagated layer-1 facet content.) -/
theorem dcp_facets_valid : FacetFamilyValid demoP demoR demoXl demoXu dcpBS := by
  intro S x hbox
  have hfull : (∑ i, relu (linVal (demoP i) x (demoR i))) ≤ 3 := by
    have h := demo_joint_cut_le x hbox
    simpa only [demoCC, demoB, one_mul] using h
  have hsub : (∑ i ∈ S, relu (linVal (demoP i) x (demoR i)))
      ≤ ∑ i, relu (linVal (demoP i) x (demoR i)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro i _ _
    unfold relu
    exact le_max_left _ _
  show (∑ i ∈ S, relu (linVal (demoP i) x (demoR i))) ≤ 3
  linarith

/-- **The propagated bound `B₂(P_cut) = 3` is VALID**: over the cut polytope,
the layer-2 objective `relu (a₁ + a₂ + a₃)` never exceeds 3 (one facet
application — the layer-1 facet has become a layer-2 premise). -/
theorem dcp_B2cut_valid :
    ∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
      CutFeasible demoP demoR demoXl demoXu dcpLz dcpUz dcpBS x z a →
      (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ 3 := by
  intro x z a h
  have hsum : a 0 + a 1 + a 2 ≤ 3 := by
    have hfac := h.2 Finset.univ
    simpa only [dcpBS, Fin.sum_univ_three] using hfac
  have hobj : (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i))
      = relu (a 0 + a 1 + a 2) := by
    simp [dcpDD, dcpV, dcpB2, Fin.sum_univ_three]
  rw [hobj]
  unfold relu
  exact max_le (by norm_num) hsum

/-- The genuine attainment point `x* = (−1, 1)`. -/
def dcpXstar : Fin 2 → ℚ
  | 0 => -1
  | 1 => 1

/-- **The propagated bound 3 is EXACT**: it is attained by the genuine
execution at `x* = (−1,1)` (where `z = (−1,3,−1)` and the objective is
`relu 3 = 3`), so no `P_cut`-valid bound can be below 3. -/
theorem dcp_B2cut_floor :
    ∀ B : ℚ,
      (∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
        CutFeasible demoP demoR demoXl demoXu dcpLz dcpUz dcpBS x z a →
        (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ B) →
      3 ≤ B := by
  intro B hB
  have hbox : ∀ j, demoXl j ≤ dcpXstar j ∧ dcpXstar j ≤ demoXu j := by
    intro j
    fin_cases j <;> exact ⟨by norm_num [demoXl, dcpXstar], by norm_num [demoXu, dcpXstar]⟩
  have hfeas := genuine_in_cut_polytope demoP demoR demoXl demoXu dcpLz dcpUz
    dcpBS dcp_lz_sound dcp_uz_sound dcp_unstable dcp_facets_valid dcpXstar hbox
  have hle : (∑ i, dcpDD i * relu ((∑ t, dcpV i t *
      relu (linVal (demoP t) dcpXstar (demoR t))) + dcpB2 i)) ≤ B :=
    hB dcpXstar _ _ hfeas
  have e0 : relu (linVal (demoP 0) dcpXstar (demoR 0)) = 0 := by
    have hv : linVal (demoP 0) dcpXstar (demoR 0) = -1 := by
      norm_num [linVal, demoP, demoR, dcpXstar, Fin.sum_univ_two]
    rw [hv]
    unfold relu
    exact max_eq_left (by norm_num)
  have e1 : relu (linVal (demoP 1) dcpXstar (demoR 1)) = 3 := by
    have hv : linVal (demoP 1) dcpXstar (demoR 1) = 3 := by
      norm_num [linVal, demoP, demoR, dcpXstar, Fin.sum_univ_two]
    rw [hv]
    unfold relu
    exact max_eq_right (by norm_num)
  have e2 : relu (linVal (demoP 2) dcpXstar (demoR 2)) = 0 := by
    have hv : linVal (demoP 2) dcpXstar (demoR 2) = -1 := by
      norm_num [linVal, demoP, demoR, dcpXstar, Fin.sum_univ_two]
    rw [hv]
    unfold relu
    exact max_eq_left (by norm_num)
  have heval : (∑ i, dcpDD i * relu ((∑ t, dcpV i t *
      relu (linVal (demoP t) dcpXstar (demoR t))) + dcpB2 i)) = 3 := by
    simp only [dcpDD, dcpV, dcpB2, Fin.sum_univ_one, Fin.sum_univ_three,
      one_mul, add_zero, e0, e1, e2, zero_add]
    unfold relu
    exact max_eq_right (by norm_num)
  rw [heval] at hle
  exact hle

/-! ### 7b.  The §8 zU-substitution construction on the same instance. -/

/-- Per-neuron CROWN upper chord at the demo bounds (slope `1/2` for all
three neurons: `u/(u−l) = 1/2` at `(−1,1)` and `(−3,3)`). -/
def dcpChord (t : Fin 3) (x : Fin 2 → ℚ) : ℚ :=
  (1/2) * (linVal (demoP t) x (demoR t) - dcpLz t)

/-- The substituted layer-2 upper line `zU(x) = ∑_t v_t · chord_t(x) + b2`
(the §8 construction: CROWN's per-neuron zU lines replace the coupled
post-activations). -/
def dcpZU (x : Fin 2 → ℚ) : ℚ :=
  (∑ t, dcpV 0 t * dcpChord t x) + dcpB2 0

/-- Each chord is a sound per-neuron ReLU upper bound on the box
(`Basic.relu_upper`). -/
theorem dcp_chord_sound : ∀ (t : Fin 3) (x : Fin 2 → ℚ),
    (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
    relu (linVal (demoP t) x (demoR t)) ≤ dcpChord t x := by
  intro t x hbox
  have hlz0 : dcpLz t < 0 := by fin_cases t <;> norm_num [dcpLz]
  have huz0 : 0 < dcpUz t := by fin_cases t <;> norm_num [dcpUz]
  have hs : (1/2 : ℚ) * (dcpUz t - dcpLz t) = dcpUz t := by
    fin_cases t <;> norm_num [dcpLz, dcpUz]
  have hl := dcp_lz_sound t x hbox
  have hu := dcp_uz_sound t x hbox
  unfold dcpChord
  exact relu_upper (dcpLz t) (dcpUz t) (1/2) _ hlz0 huz0 hs hl hu

private theorem dcp_relu_mono {a b : ℚ} (h : a ≤ b) : relu a ≤ relu b := by
  unfold relu
  exact max_le_max (le_refl 0) h

/-- **Fairness leg**: the zU-substitution value `relu (zU(x))` is itself a
sound bound on the genuine objective at every box point — the §8 construction
is a real competitor, not a strawman. -/
theorem dcp_zU_sound : ∀ x : Fin 2 → ℚ,
    (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
    (∑ i, dcpDD i * relu ((∑ t, dcpV i t *
        relu (linVal (demoP t) x (demoR t))) + dcpB2 i))
      ≤ relu (dcpZU x) := by
  intro x hbox
  have hinner : (∑ t, dcpV 0 t * relu (linVal (demoP t) x (demoR t))) + dcpB2 0
      ≤ dcpZU x := by
    unfold dcpZU
    have hterm : ∀ t ∈ (Finset.univ : Finset (Fin 3)),
        dcpV 0 t * relu (linVal (demoP t) x (demoR t))
          ≤ dcpV 0 t * dcpChord t x := by
      intro t _
      simp only [dcpV, one_mul]
      exact dcp_chord_sound t x hbox
    have hsum := Finset.sum_le_sum hterm
    linarith
  have hmono := dcp_relu_mono hinner
  calc (∑ i, dcpDD i * relu ((∑ t, dcpV i t *
          relu (linVal (demoP t) x (demoR t))) + dcpB2 i))
      = relu ((∑ t, dcpV 0 t * relu (linVal (demoP t) x (demoR t))) + dcpB2 0) := by
        simp only [dcpDD, Fin.sum_univ_one, one_mul]
    _ ≤ relu (dcpZU x) := hmono

/-- The zU-substitution bound evaluates to at most 4 on the box:
`zU(x) = (7 − x₁)/2 ≤ 4`. -/
theorem dcp_zU_le_four : ∀ x : Fin 2 → ℚ,
    (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
    relu (dcpZU x) ≤ 4 := by
  intro x hbox
  obtain ⟨h0l, h0u⟩ := hbox 0
  simp only [demoXl, demoXu] at h0l h0u
  have hval : dcpZU x = (7 - x 0) / 2 := by
    simp only [dcpZU, dcpChord, dcpV, dcpB2, dcpLz, linVal, demoP, demoR,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, add_zero, one_mul]
    ring
  rw [hval]
  unfold relu
  apply max_le (by norm_num)
  linarith

/-- The witness `x = (−1, 0)` attaining the zU maximum. -/
def dcpXzu : Fin 2 → ℚ
  | 0 => -1
  | 1 => 0

/-- **The §8 construction's value is EXACTLY 4**: any bound dominating
`relu (zU(·))` over the box is `≥ 4` (attained at `x = (−1,0)`).  Together
with `dcp_zU_le_four` this pins `B₂(zU-substitution) = 4`. -/
theorem dcp_zU_floor :
    ∀ B : ℚ, (∀ x : Fin 2 → ℚ, (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
        relu (dcpZU x) ≤ B) → 4 ≤ B := by
  intro B hB
  have hbox : ∀ j, demoXl j ≤ dcpXzu j ∧ dcpXzu j ≤ demoXu j := by
    intro j
    fin_cases j <;> exact ⟨by norm_num [demoXl, dcpXzu], by norm_num [demoXu, dcpXzu]⟩
  have hle := hB dcpXzu hbox
  have hval : dcpZU dcpXzu = 4 := by
    simp only [dcpZU, dcpChord, dcpV, dcpB2, dcpLz, linVal, demoP, demoR,
      dcpXzu, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, add_zero, one_mul]
    norm_num
  have heval : relu (dcpZU dcpXzu) = 4 := by
    rw [hval]
    unfold relu
    exact max_eq_right (by norm_num)
  rw [heval] at hle
  exact hle

/-! ### 7c.  Triangle-only floor: even the BEST `P_tri` bound is ≥ 7/2. -/

/-- The triangle-only relaxation witness input `x = (0, −1)`. -/
def dcpXtri : Fin 2 → ℚ
  | 0 => 0
  | 1 => -1

/-- The witness pre-activations `z = (0, −2, 2)`. -/
def dcpZtri : Fin 3 → ℚ
  | 0 => 0
  | 1 => -2
  | 2 => 2

/-- The witness post-activations `a = (1/2, 1/2, 5/2)` (each triangle-tight,
jointly violating the 3-cut — the sealed `demoA` witness of
`MultiReluCutK.demo_pairwise_relaxation_open`). -/
def dcpAtri : Fin 3 → ℚ
  | 0 => 1/2
  | 1 => 1/2
  | 2 => 5/2

/-- The witness is `P_tri`-feasible. -/
theorem dcp_tri_witness_feasible :
    TriFeasible demoP demoR demoXl demoXu dcpLz dcpUz dcpXtri dcpZtri dcpAtri := by
  unfold TriFeasible
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> exact ⟨by norm_num [demoXl, dcpXtri], by norm_num [demoXu, dcpXtri]⟩
  · intro i
    fin_cases i <;>
    · simp only [dcpZtri, dcpXtri, demoP, demoR, linVal, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
      norm_num
  · intro i
    fin_cases i <;>
    · refine ⟨by norm_num [dcpAtri], by norm_num [dcpZtri, dcpAtri], ?_⟩
      norm_num [dcpAtri, dcpZtri, dcpLz, dcpUz]

/-- **Triangle-only floor**: NO bound valid over `P_tri` is below `7/2` — the
witness point has objective `relu (1/2 + 1/2 + 5/2) = 7/2`.  Hence the best
triangle-only bound is `≥ 7/2 > 3 = B₂(P_cut)`. -/
theorem dcp_tri_floor :
    ∀ B : ℚ,
      (∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
        TriFeasible demoP demoR demoXl demoXu dcpLz dcpUz x z a →
        (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ B) →
      7/2 ≤ B := by
  intro B hB
  have hle := hB dcpXtri dcpZtri dcpAtri dcp_tri_witness_feasible
  have heval : (∑ i, dcpDD i * relu ((∑ t, dcpV i t * dcpAtri t) + dcpB2 i))
      = 7/2 := by
    have hsum : (∑ t, dcpV 0 t * dcpAtri t) + dcpB2 0 = 7/2 := by
      simp only [dcpV, dcpB2, dcpAtri, Fin.sum_univ_three, one_mul, add_zero]
      norm_num
    simp only [dcpDD, Fin.sum_univ_one, one_mul, hsum]
    unfold relu
    exact max_eq_right (by norm_num)
  rw [heval] at hle
  exact hle

/-! ## 8.  The strict-instance packaging theorems. -/

/-- **`deep_cut_strict_instance` (synthetic mechanism demo).**  On the sealed
k = 3 coupling instance feeding `z² = a₁+a₂+a₃`:
(i) the PROPAGATED bound 3 is valid over `P_cut`;
(ii) the §8 zU-substitution construction cannot certify any bound below 4
(its value is exactly 4 — see `dcp_zU_le_four` for the matching upper half);
(iii) 3 < 4 — facet propagation is STRICTLY tighter than zU substitution:
propagating the layer-1 facets retains exactly the 3-way coupling content
that CROWN's per-neuron zU lines spend. -/
theorem deep_cut_strict_instance :
    (∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
        CutFeasible demoP demoR demoXl demoXu dcpLz dcpUz dcpBS x z a →
        (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ 3) ∧
    (∀ B : ℚ, (∀ x : Fin 2 → ℚ, (∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) →
        relu (dcpZU x) ≤ B) → 4 ≤ B) ∧
    ((3:ℚ) < 4) :=
  ⟨dcp_B2cut_valid, dcp_zU_floor, by norm_num⟩

/-- **`deep_cut_strict_vs_triangle` (stronger).**  The propagated bound 3 is
strictly below EVERY valid triangle-only bound (floor 7/2), not merely below
the particular zU construction: the strict gap is intrinsic to dropping the
facets, certifying the conjectured mechanism ("CROWN's own upper bounds have
spent the coupling; the facets encode it"). -/
theorem deep_cut_strict_vs_triangle :
    (∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
        CutFeasible demoP demoR demoXl demoXu dcpLz dcpUz dcpBS x z a →
        (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ 3) ∧
    (∀ B : ℚ,
      (∀ (x : Fin 2 → ℚ) (z a : Fin 3 → ℚ),
        TriFeasible demoP demoR demoXl demoXu dcpLz dcpUz x z a →
        (∑ i, dcpDD i * relu ((∑ t, dcpV i t * a t) + dcpB2 i)) ≤ B) →
      7/2 ≤ B) ∧
    ((3:ℚ) < 7/2) :=
  ⟨dcp_B2cut_valid, dcp_tri_floor, by norm_num⟩

/-! ## Trust-base check.

Every theorem below must report exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no domain axioms. -/

#print axioms dcp_relu_chord_sound
#print axioms genuine_in_cut_polytope
#print axioms deep_cut_propagation_sound
#print axioms cutFeasible_triFeasible
#print axioms deep_cut_dominates_triangle
#print axioms facet_bound_of_corners
#print axioms deepCut_as_farkas_premise
#print axioms dcp_lz_sound
#print axioms dcp_uz_sound
#print axioms dcp_unstable
#print axioms dcp_facets_valid
#print axioms dcp_B2cut_valid
#print axioms dcp_B2cut_floor
#print axioms dcp_chord_sound
#print axioms dcp_zU_sound
#print axioms dcp_zU_le_four
#print axioms dcp_zU_floor
#print axioms dcp_tri_witness_feasible
#print axioms dcp_tri_floor
#print axioms deep_cut_strict_instance
#print axioms deep_cut_strict_vs_triangle

end Crownproof
