/-
  # multiReluCut_box_exact — the per-domain joint-cut bound is EXACT and has an
  # O(2^k·n) closed form (no corner enumeration)

  Invention-wave-1 PROVE lane.  Sealed conjecture record:
  `data/provenance/invention-wave-1-conjectures-2026-06-11.json`
  (set sha256 00b2f585d355e1b4abc2eb2ab6722dd1375ff65619a905d722da5c7cd4b6e8b4),
  conjecture "multiReluCut_box_exact — the per-domain joint-cut bound is EXACT
  and has an O(2^k·n) closed form (no corner enumeration)", angle
  tighter-relaxations, per-conjecture sha256
  aaeffa73f44e91ab954d5869b3183ddb94a410cfa0580bb5d3797b55d506c4e4.

  ## Statement (as conjectured — proved AS STATED, no weakening)

  For k neurons with pre-activations `z_i = linVal (p i) x (r i)` affine over an
  n-box `[xl,xu]` and cut weights `cc_i ≥ 0`, the EXACT supremum of
  `∑_i cc_i · relu (z_i x)` over the box equals

      max over the 2^k activation patterns S of
        `patternBound S = ∑_{i∈S} cc_i r_i
                          + ∑_j [ (∑_{i∈S} cc_i p_ij) · mid_j
                                  + |∑_{i∈S} cc_i p_ij| · rad_j ]`

  (`mid = (xu+xl)/2`, `rad = (xu−xl)/2`), and it is ATTAINED at the explicit box
  corner `cornerOf w⋆ xl xu` of the argmax pattern's assembled weight vector
  `w⋆_j = ∑_{i∈S⋆} cc_i p_ij` (coordinate j pushed to `xu j` iff `w⋆_j ≥ 0`).
  Stated as `IsGreatest` — both supremum-validity AND attainment.

  Consequences proved here:
    * `multiReluCut_le_patternMax` — the pattern-max is a VALID joint cut bound
      (usable as the `B` of `multiReluCut_box_le` / `multiReluCut_bridge`),
      computable by a per-pattern weight scan: one `boxMaxAffine` evaluation per
      pattern = O(n) each, O(2^k·n) total — NO 2^n corner enumeration.
    * `multiReluCut_box_exact` — the pattern-max is the exact supremum,
      attained at an explicit corner (`IsGreatest`).
    * `patternMax_le_of_valid_bound` — it is the LEAST valid bound: every B
      valid on the box dominates it.  So within the value-cut family this is
      the TIGHTEST joint value-cut the family can contribute per leaf.

  ## Formalization delta vs the sealed sketch

  NONE in the theorem statement: `boxMaxAffine`, `patternBound`, and
  `multiReluCut_box_exact` are verbatim from the sealed sketch (up to
  parenthesization `(Finset.univ.powerset).sup'`).  Additions are auxiliary
  only: `cornerOf` (the explicit attaining corner, named so attainment is
  visible in the artifact), the interval-arithmetic lemma
  `linVal_le_boxMaxAffine`, its attainment converse `linVal_cornerOf`, the
  weighted pattern-vs-relu comparison `weighted_pattern_le_relu_sum`, the
  active-set identity `relu_sum_eq_active_pattern` (the `hsplit` of
  `multiReluCut_pattern_dominance`, extracted as a standalone equality), and
  the two consequence theorems.  Note `hcc`/`hbox` are needed only for the
  attainment half; the upper-bound half (`multiReluCut_le_patternMax`) holds
  for arbitrary `cc` and an arbitrary (possibly empty) box.

  ## Honesty / novelty tier

  N1 AT MOST, "first formalization in this program" — NOT new mathematics.
  The closed form is standard interval arithmetic for an affine functional;
  exactness via activation-pattern enumeration is folklore in the
  kReLU/GCP-CROWN literature.  The value here is the machine-checked
  IsGreatest (exactness + explicit attaining corner) compatible with the
  existing `multiReluCut_bridge` Farkas premise, replacing the 2^k·2^n
  corner enumeration of `multiReluCut_box_le` by an O(2^k·n) scan.  §11's
  load-bearing caveat is unchanged: this is per-leaf LP-optimality WITHIN the
  value-cut family, not a blanket domain-reduction claim; it moves zero
  VNN-COMP scored points by itself.

  ## Axioms

  All `#print axioms` below report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axioms
  (verified via `lake build`; see the `#print axioms` commands at the bottom).
-/

import Crownproof.MultiReluCutK
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace Crownproof

open Finset

/-! ## 1.  The closed form and the attaining corner -/

/-- Closed-form box-max of an affine functional (interval-arithmetic form):
`rr + ∑_j (w_j · mid_j + |w_j| · rad_j)` with `mid = (xu+xl)/2`, `rad = (xu−xl)/2`.
Evaluating it is O(n) — no corner enumeration. -/
def boxMaxAffine {n : ℕ} (w : Fin n → ℚ) (rr : ℚ) (xl xu : Fin n → ℚ) : ℚ :=
  rr + ∑ j, (w j * ((xu j + xl j) / 2) + |w j| * ((xu j - xl j) / 2))

/-- The per-pattern closed-form bound: `boxMaxAffine` of the pattern-assembled
affine form `∑_{i∈S} cc_i · z_i`. -/
def patternBound {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (S : Finset (Fin k)) : ℚ :=
  boxMaxAffine (fun j => ∑ i ∈ S, cc i * p i j) (∑ i ∈ S, cc i * r i) xl xu

/-- The explicit box corner maximizing the affine functional with weight `w`:
coordinate `j` is pushed to `xu j` iff `w j ≥ 0`, else to `xl j`. -/
def cornerOf {n : ℕ} (w xl xu : Fin n → ℚ) : Fin n → ℚ :=
  fun j => if 0 ≤ w j then xu j else xl j

/-- The maximizing corner lies in the box. -/
theorem cornerOf_mem_box {n : ℕ} (w xl xu : Fin n → ℚ) (hbox : ∀ j, xl j ≤ xu j) :
    ∀ j, xl j ≤ cornerOf w xl xu j ∧ cornerOf w xl xu j ≤ xu j := by
  intro j
  unfold cornerOf
  rcases le_or_gt 0 (w j) with h | h
  · rw [if_pos h]; exact ⟨hbox j, le_refl _⟩
  · rw [if_neg (not_le.mpr h)]; exact ⟨le_refl _, hbox j⟩

/-- **Interval-arithmetic upper bound.**  An affine functional on the box is
dominated by its closed-form box-max: for `x ∈ [xl,xu]`,
`linVal w x rr ≤ boxMaxAffine w rr xl xu`.  Per coordinate this is
`w_j·(x_j − mid_j) ≤ |w_j|·rad_j`. -/
theorem linVal_le_boxMaxAffine {n : ℕ} (w : Fin n → ℚ) (rr : ℚ) (xl xu x : Fin n → ℚ)
    (hx : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    linVal w x rr ≤ boxMaxAffine w rr xl xu := by
  unfold linVal boxMaxAffine
  have hsum : (∑ j, w j * x j)
      ≤ ∑ j, (w j * ((xu j + xl j) / 2) + |w j| * ((xu j - xl j) / 2)) := by
    apply Finset.sum_le_sum
    intro j _
    have h1 : |x j - (xu j + xl j) / 2| ≤ (xu j - xl j) / 2 := by
      rw [abs_le]
      constructor
      · linarith [(hx j).1]
      · linarith [(hx j).2]
    have h2 : w j * (x j - (xu j + xl j) / 2) ≤ |w j| * ((xu j - xl j) / 2) :=
      calc w j * (x j - (xu j + xl j) / 2)
          ≤ |w j * (x j - (xu j + xl j) / 2)| := le_abs_self _
        _ = |w j| * |x j - (xu j + xl j) / 2| := abs_mul _ _
        _ ≤ |w j| * ((xu j - xl j) / 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  linarith

/-- **Attainment.**  At the explicit corner `cornerOf w xl xu` the affine
functional EQUALS its closed-form box-max: per coordinate,
`w_j · corner_j = w_j · mid_j + |w_j| · rad_j`. -/
theorem linVal_cornerOf {n : ℕ} (w : Fin n → ℚ) (rr : ℚ) (xl xu : Fin n → ℚ) :
    linVal w (cornerOf w xl xu) rr = boxMaxAffine w rr xl xu := by
  unfold linVal boxMaxAffine cornerOf
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases le_or_gt 0 (w j) with h | h
  · rw [if_pos h, abs_of_nonneg h]; ring
  · rw [if_neg (not_le.mpr h), abs_of_neg h]; ring

/-! ## 2.  The two halves of the pointwise identity
`∑ cc_i·relu z_i = max_S ∑_{i∈S} cc_i·z_i` -/

/-- `≥` half: every per-pattern weighted sum is dominated by the full weighted
ReLU sum (drop negative parts inside `S`, drop nonnegative terms outside `S`;
both steps need `cc ≥ 0`). -/
theorem weighted_pattern_le_relu_sum {k : ℕ} (cc z : Fin k → ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (S : Finset (Fin k)) :
    (∑ i ∈ S, cc i * z i) ≤ (∑ i, cc i * relu (z i)) :=
  calc (∑ i ∈ S, cc i * z i)
      ≤ (∑ i ∈ S, cc i * relu (z i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (le_max_right 0 (z i)) (hcc i)
    _ ≤ (∑ i, cc i * relu (z i)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro i _ _
        exact mul_nonneg (hcc i) (le_max_left 0 (z i))

/-- `=` half at the active set: the weighted ReLU sum EQUALS the per-pattern
weighted sum over the active set `A = {i : 0 ≤ z i}`.  (This is the `hsplit`
inside `multiReluCut_pattern_dominance`, extracted as a standalone equality.
No sign condition on `cc` is needed.) -/
theorem relu_sum_eq_active_pattern {k : ℕ} (cc z : Fin k → ℚ) :
    (∑ i, cc i * relu (z i))
      = (∑ i ∈ Finset.univ.filter (fun i => 0 ≤ z i), cc i * z i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold relu
  rcases le_or_gt 0 (z i) with h | h
  · rw [if_pos h, max_eq_right h]
  · rw [if_neg (not_le.mpr h), max_eq_left (le_of_lt h), mul_zero]

/-! ## 3.  Upper bound: the O(2^k·n) pattern-max is a valid joint cut bound -/

/-- **Valid joint cut bound, closed form.**  For every `x` in the box, the
weighted ReLU sum is dominated by the max over the `2^k` patterns of the
closed-form `patternBound` — computable by a weight scan in O(2^k·n), with NO
corner enumeration.  (Holds for arbitrary `cc`, arbitrary box: the active-set
identity and interval arithmetic need no sign or nonemptiness conditions.)
This value is therefore usable as the `B` of `multiReluCut_box_le` /
`multiReluCut_bridge`. -/
theorem multiReluCut_le_patternMax {n k : ℕ}
    (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ)
    (x : Fin n → ℚ) (hx : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    (∑ i, cc i * relu (linVal (p i) x (r i)))
      ≤ (Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
          (patternBound cc p r xl xu) := by
  have h1 : (∑ i, cc i * relu (linVal (p i) x (r i)))
      = ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ linVal (p i) x (r i)),
          cc i * linVal (p i) x (r i) :=
    relu_sum_eq_active_pattern cc (fun i => linVal (p i) x (r i))
  rw [h1, pattern_affine_assemble cc p r x]
  refine le_trans (linVal_le_boxMaxAffine _ _ xl xu x hx) ?_
  exact Finset.le_sup' (patternBound cc p r xl xu)
    (Finset.mem_powerset.mpr (Finset.subset_univ _))

/-! ## 4.  The main theorem: EXACTNESS (IsGreatest) with explicit attainment -/

/-- **The per-domain joint-cut bound is EXACT.**  The supremum of
`∑_i cc_i · relu (z_i x)` over the box `[xl,xu]` is EXACTLY the max over the
`2^k` activation patterns of the closed-form `patternBound`, and it is
ATTAINED (membership half of `IsGreatest`) at the explicit corner
`cornerOf w⋆ xl xu` of the argmax pattern's assembled weight vector `w⋆`.
So the corner-derived `B` of `multiReluCut_box_le`, taken at this max, is the
TIGHTEST possible joint value-cut bound — and it is computable in O(2^k·n). -/
theorem multiReluCut_box_exact {n k : ℕ}
    (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (hcc : ∀ i, 0 ≤ cc i) (hbox : ∀ j, xl j ≤ xu j) :
    IsGreatest
      {v : ℚ | ∃ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
               v = ∑ i, cc i * relu (linVal (p i) x (r i))}
      ((Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (patternBound cc p r xl xu)) := by
  constructor
  · -- Membership: the max is ATTAINED at the corner of the argmax pattern.
    obtain ⟨S, hSmem, hSeq⟩ :=
      Finset.exists_mem_eq_sup'
        (⟨∅, Finset.empty_mem_powerset _⟩ :
          (Finset.univ.powerset (α := Fin k)).Nonempty)
        (patternBound cc p r xl xu)
    refine ⟨cornerOf (fun j => ∑ i ∈ S, cc i * p i j) xl xu,
            cornerOf_mem_box _ xl xu hbox, ?_⟩
    have hle := multiReluCut_le_patternMax cc p r xl xu
      (cornerOf (fun j => ∑ i ∈ S, cc i * p i j) xl xu)
      (cornerOf_mem_box _ xl xu hbox)
    rw [hSeq] at hle ⊢
    refine le_antisymm ?_ hle
    -- patternBound S = boxMaxAffine w⋆ = linVal w⋆ (corner) = ∑_{i∈S} cc_i·z_i(corner)
    --                ≤ ∑_i cc_i·relu (z_i (corner)).
    unfold patternBound
    rw [← linVal_cornerOf (fun j => ∑ i ∈ S, cc i * p i j)
          (∑ i ∈ S, cc i * r i) xl xu,
        ← pattern_affine_assemble cc p r
          (cornerOf (fun j => ∑ i ∈ S, cc i * p i j) xl xu) S]
    exact weighted_pattern_le_relu_sum cc _ hcc S
  · -- Upper bound: every box value is dominated by the pattern-max.
    rintro v ⟨x, hx, rfl⟩
    exact multiReluCut_le_patternMax cc p r xl xu x hx

/-! ## 5.  Tightness: the pattern-max is the LEAST valid bound -/

/-- **Per-leaf LP-optimality within the value-cut family.**  Every bound `B`
valid for the weighted ReLU sum on the whole box dominates the pattern-max.
Together with `multiReluCut_le_patternMax` (validity) this says the O(2^k·n)
closed form is the TIGHTEST joint value-cut bound the family can contribute,
folded through `multiReluCut_bridge` as one `≥ 0`-multiplier Farkas premise. -/
theorem patternMax_le_of_valid_bound {n k : ℕ}
    (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hvalid : ∀ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
              (∑ i, cc i * relu (linVal (p i) x (r i))) ≤ B) :
    (Finset.univ.powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩
      (patternBound cc p r xl xu) ≤ B := by
  obtain ⟨x, hx, hfx⟩ := (multiReluCut_box_exact cc p r xl xu hcc hbox).1
  rw [hfx]
  exact hvalid x hx

/-
  Expected output of every `#print axioms` below (verified via `lake build`):

    'Crownproof.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]

  No `sorryAx`, no domain-specific axioms.
-/
#print axioms cornerOf_mem_box
#print axioms linVal_le_boxMaxAffine
#print axioms linVal_cornerOf
#print axioms weighted_pattern_le_relu_sum
#print axioms relu_sum_eq_active_pattern
#print axioms multiReluCut_le_patternMax
#print axioms multiReluCut_box_exact
#print axioms patternMax_le_of_valid_bound

end Crownproof
