/-
  INVENTION WAVE 1 — `gap_closed_form` + `gap_pos_iff_sign_disagree`
  (PHASE2 Pillar D's T-GAP as a theorem.)

  Sealed conjecture: data/provenance/invention-wave-1-conjectures-2026-06-11.json,
  angle "TIGHTER RELAXATIONS", conjecture 2.

  ## What this file proves, sorry-free

  Let `uzExact p r xl xu i = boxMaxAffine (p i) (r i) xl xu` be the EXACT box
  maximum of neuron `i`'s affine pre-activation `z_i = linVal (p i) x (r i)` over
  the input box `[xl, xu]` (exactness is itself proved here: `le_boxMaxAffine`
  soundness + `boxMaxAffine_attained` attainment at a box corner).  Let
  `patternBound cc p r xl xu S = boxMaxAffine` of the assembled pattern row
  `∑_{i∈S} cc_i·p_i` — the per-pattern closed-form bound whose `sup'` over all
  `2^k` patterns is the closed-form joint-cut bound (`jointCut_le_patternSup`
  grounds it: it IS a valid bound for `∑ cc_i·relu z_i` on the whole box, via the
  existing `multiReluCut_pattern_dominance` machinery).  Define the per-coordinate
  triangle-inequality DEFECT of the group on pattern `S`:

      coordDefect_S := ∑_j (∑_{i∈S} cc_i·|p_ij| − |∑_{i∈S} cc_i·p_ij|)·(xu_j−xl_j)/2 ≥ 0.

  1. `gap_closed_form` — in the possibly-active regime (`uzExact_i > 0`, `cc_i > 0`),
     the gap between the DECOUPLED bound `∑_i cc_i·relu(uzExact_i)` (each neuron at
     its own box sup, the `FacetCut.gapBdecoupled` notion) and the joint-cut bound
     `sup'_S patternBound_S` has the CLOSED FORM

         gap = inf'_S [ ∑_{i∉S} cc_i·uzExact_i + coordDefect_S ].

     Engine: per-pattern identity `pattern_defect_identity`
     (`∑_{i∈S} cc_i·uzExact_i − patternBound_S = coordDefect_S`, pure algebra from
     the mid/rad expansion `boxMaxAffine_midrad`), plus `sup'`/`inf'` duality.

  2. `gap_pos_iff_sign_disagree` — the weight-syntactic, decidable criterion:

         gap > 0  ⟺  ∃ coordinate j with xl_j < xu_j and rows i₁ i₂ with
                      p_{i₁j}·p_{i₂j} < 0.

     A multi-neuron value cut can strictly beat the decoupled relaxation on a box
     IFF some input coordinate is pulled in opposite directions by two group
     members.  Corollaries: `gap_nonneg` (the decoupled bound always dominates) and
     `gap_eq_zero_iff_sign_separable` (the kernel-checked SKIP rule: coordinate-
     sign-separable groups provably cannot beat the decoupled bound).

  3. Secondary closed form (NO iff claimed, per the sealed conjecture):
     `chord_slack_closed_form` — the §7-style chord functional
     `∑ cc_i·s_i·(z_i(x) − lz_i)` assembles into ONE affine row
     (`chord_slack_row_assemble`), so its exact box maximum is `boxMaxAffine` of
     that row: a closed form (sound + attained at a corner).

  4. Instance validation: `facetcut_gap_pos` — on the existing `FacetCut` k=2, n=1
     instance (`gapW = (x, −x)` on `[−1,1]`) the criterion fires (coordinate 0 is
     pulled in opposite directions), recovering `facet_gap_pos`'s strict gap
     through the general theorem.

  ## Faithfulness delta vs the sealed lean_statement_sketch (the seal is the record)

  * `boxMaxAffine` / `patternBound` do NOT exist in the committed substrate (they
    are the sealed set's Conjecture 1 carriers, a different lane).  They are
    defined HERE, locally, as `(∑_j max (w_j·xl_j) (w_j·xu_j)) + r` and proven to
    deserve the name "exact box max" (`le_boxMaxAffine`, `boxMaxAffine_attained`).
    The Conjecture-1 lane is landing the same carriers IN PARALLEL (uncommitted at
    write time) as `Crownproof.boxMaxAffine` in mid/rad form — provably equal to
    this file's max-of-endpoints form (`boxMaxAffine_midrad` is exactly that
    bridge, modulo `ring`).  This file stays self-contained to be safe against
    commit ordering; carrier reconciliation is a one-lemma wave-merge follow-up.
  * Namespace is `Crownproof.InventionWave1` (not bare `Crownproof`) to avoid
    cross-lane name collisions with the Conjecture-1 lane over the shared carrier
    names.  Statement shapes are otherwise as sketched.
  * `gap_pos_iff_sign_disagree`'s elided hypotheses (`…` in the sketch) are the
    same `hcc`/`hbox`/`hunst` as `gap_closed_form`.
  * `hcc` is carried in `gap_closed_form` to match the sealed statement; the
    equality itself only needs `hbox` + `hunst` (the defect identity is sign-free).
    The iff genuinely uses all three.

  ## Honesty (novelty-tier standard, designs/2026-06-11-graduation-v3-valueless-carriers.md)

  * N1 at most — FIRST FORMALIZATION claim only.  The qualitative insight "cuts
    help iff neurons are coupled" is published informally (kReLU NeurIPS 2019,
    PRIMA POPL 2022, GCP-CROWN); the closed-form min formula and the verified
    syntactic iff are claimed as formalized-first pending the literature leg,
    NEVER as new mathematics.
  * Regime honesty: the iff is against the DECOUPLED/interval baseline
    (`FacetCut.gapBdecoupled` notion), NOT the §7 chord-LP slack — for the chord
    functional only the closed FORM is claimed (item 3), no iff.  A positive gap
    licenses no Δdomains claim by itself (PHASE2 §11 knife-edge caveat stands).
  * Zero VNN-COMP scored points; theory contribution only.

  All `#print axioms` below must be `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.
-/

import Crownproof.Basic
import Crownproof.MultiReluCutK
import Crownproof.FacetCut
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Crownproof
namespace InventionWave1

open Finset

/-! ## 0.  The closed-form carriers: exact affine box max, pattern bound, defect. -/

/-- The EXACT maximum of the affine functional `linVal w · r` over the box
`[xl, xu]`: per coordinate, take the better endpoint.  An `O(n)` closed form —
no corner enumeration.  ("Exact" is proved, not assumed: `le_boxMaxAffine` +
`boxMaxAffine_attained`.) -/
def boxMaxAffine {n : ℕ} (w : Fin n → ℚ) (r : ℚ) (xl xu : Fin n → ℚ) : ℚ :=
  (∑ j, max (w j * xl j) (w j * xu j)) + r

/-- The per-pattern closed-form bound: `boxMaxAffine` of the assembled pattern row
`∑_{i∈S} cc_i·p_i` with intercept `∑_{i∈S} cc_i·r_i`. -/
def patternBound {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (S : Finset (Fin k)) : ℚ :=
  boxMaxAffine (fun j => ∑ i ∈ S, cc i * p i j) (∑ i ∈ S, cc i * r i) xl xu

/-- Neuron `i`'s exact pre-activation box maximum. -/
def uzExact {n k : ℕ} (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (i : Fin k) : ℚ := boxMaxAffine (p i) (r i) xl xu

/-- The per-coordinate triangle-inequality DEFECT of the group on pattern `S`:
how much the assembled row's reach falls short of the sum of the members'
independent reaches, coordinate by coordinate. -/
def coordDefect {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (xl xu : Fin n → ℚ) (S : Finset (Fin k)) : ℚ :=
  ∑ j, ((∑ i ∈ S, cc i * |p i j|) - |∑ i ∈ S, cc i * p i j|) * ((xu j - xl j) / 2)

/-! ## 1.  `boxMaxAffine` IS the exact box max: sound and attained. -/

/-- Soundness: `boxMaxAffine` dominates the affine functional at every box point. -/
theorem le_boxMaxAffine {n : ℕ} (w : Fin n → ℚ) (r : ℚ) (xl xu x : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    linVal w x r ≤ boxMaxAffine w r xl xu := by
  unfold linVal boxMaxAffine
  have h : ∀ j ∈ Finset.univ, w j * x j ≤ max (w j * xl j) (w j * xu j) := by
    intro j _
    obtain ⟨hl, hu⟩ := hbox j
    rcases le_or_gt 0 (w j) with hw | hw
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hu hw)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hl (le_of_lt hw))
  have hsum := Finset.sum_le_sum h
  linarith

/-- Attainment: `boxMaxAffine` is achieved at the sign-optimal box corner. -/
theorem boxMaxAffine_attained {n : ℕ} (w : Fin n → ℚ) (r : ℚ) (xl xu : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ xu j) :
    ∃ y : Fin n → ℚ, (∀ j, y j = xl j ∨ y j = xu j) ∧
      linVal w y r = boxMaxAffine w r xl xu := by
  refine ⟨fun j => if 0 ≤ w j then xu j else xl j, fun j => ?_, ?_⟩
  · by_cases h : 0 ≤ w j
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  · unfold linVal boxMaxAffine
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    show w j * (if 0 ≤ w j then xu j else xl j) = max (w j * xl j) (w j * xu j)
    by_cases h : 0 ≤ w j
    · rw [if_pos h, max_eq_right (mul_le_mul_of_nonneg_left (hbox j) h)]
    · rw [if_neg h,
          max_eq_left (mul_le_mul_of_nonpos_left (hbox j) (le_of_lt (not_le.mp h)))]

/-- Mid/rad (center–radius) expansion of the exact box max:
`boxMaxAffine w r = ∑_j (w_j·mid_j + |w_j|·rad_j) + r`. -/
theorem boxMaxAffine_midrad {n : ℕ} (w : Fin n → ℚ) (r : ℚ) (xl xu : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ xu j) :
    boxMaxAffine w r xl xu
      = (∑ j, (w j * ((xl j + xu j) / 2) + |w j| * ((xu j - xl j) / 2))) + r := by
  unfold boxMaxAffine
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases le_or_gt 0 (w j) with h | h
  · rw [max_eq_right (mul_le_mul_of_nonneg_left (hbox j) h), abs_of_nonneg h]; ring
  · rw [max_eq_left (mul_le_mul_of_nonpos_left (hbox j) (le_of_lt h)), abs_of_neg h]; ring

/-- Grounding: `sup'` of the pattern bounds IS a valid joint-cut bound for the
weighted ReLU sum on the whole box — through the existing
`multiReluCut_pattern_dominance` + `pattern_affine_assemble` machinery.  (Its
EXACTNESS as a joint-cut bound is the sealed set's Conjecture 1, a different
lane; this file only needs validity to make "gap" meaningful.) -/
theorem jointCut_le_patternSup {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (hcc : ∀ i, 0 ≤ cc i)
    (x : Fin n → ℚ) (hbox : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) :
    (∑ i, cc i * relu (linVal (p i) x (r i)))
      ≤ Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
          (patternBound cc p r xl xu) := by
  apply multiReluCut_pattern_dominance cc (fun i => linVal (p i) x (r i)) _ hcc
  intro S
  rw [pattern_affine_assemble cc p r x S]
  refine le_trans (le_boxMaxAffine _ _ xl xu x hbox) ?_
  exact Finset.le_sup' (patternBound cc p r xl xu)
    (Finset.mem_powerset.mpr (Finset.subset_univ S))

/-! ## 2.  The per-pattern defect identity (the engine of the closed form). -/

/-- **Per-pattern identity**: the group members' independent reaches minus the
assembled row's reach equals the coordinate defect — pure algebra from the
mid/rad expansion (the mid parts and intercepts cancel; only the radius parts
differ, by exactly the per-coordinate triangle defect).  No sign condition on
`cc` is needed. -/
theorem pattern_defect_identity {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (hbox : ∀ j, xl j ≤ xu j)
    (S : Finset (Fin k)) :
    (∑ i ∈ S, cc i * uzExact p r xl xu i) - patternBound cc p r xl xu S
      = coordDefect cc p xl xu S := by
  have huz : ∀ i, uzExact p r xl xu i
      = (∑ j, (p i j * ((xl j + xu j) / 2) + |p i j| * ((xu j - xl j) / 2))) + r i := by
    intro i
    unfold uzExact
    exact boxMaxAffine_midrad (p i) (r i) xl xu hbox
  have hpb : patternBound cc p r xl xu S
      = (∑ j, ((∑ i ∈ S, cc i * p i j) * ((xl j + xu j) / 2)
              + |∑ i ∈ S, cc i * p i j| * ((xu j - xl j) / 2)))
        + (∑ i ∈ S, cc i * r i) := by
    unfold patternBound
    exact boxMaxAffine_midrad _ _ xl xu hbox
  have hsum : (∑ i ∈ S, cc i * uzExact p r xl xu i)
      = (∑ j, ((∑ i ∈ S, cc i * p i j) * ((xl j + xu j) / 2)
              + (∑ i ∈ S, cc i * |p i j|) * ((xu j - xl j) / 2)))
        + (∑ i ∈ S, cc i * r i) := by
    calc (∑ i ∈ S, cc i * uzExact p r xl xu i)
        = ∑ i ∈ S, ((∑ j, (cc i * p i j * ((xl j + xu j) / 2)
                          + cc i * |p i j| * ((xu j - xl j) / 2))) + cc i * r i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [huz i, mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (∑ i ∈ S, ∑ j, (cc i * p i j * ((xl j + xu j) / 2)
                          + cc i * |p i j| * ((xu j - xl j) / 2)))
            + (∑ i ∈ S, cc i * r i) := Finset.sum_add_distrib
      _ = (∑ j, ∑ i ∈ S, (cc i * p i j * ((xl j + xu j) / 2)
                          + cc i * |p i j| * ((xu j - xl j) / 2)))
            + (∑ i ∈ S, cc i * r i) := by rw [Finset.sum_comm]
      _ = (∑ j, ((∑ i ∈ S, cc i * p i j) * ((xl j + xu j) / 2)
              + (∑ i ∈ S, cc i * |p i j|) * ((xu j - xl j) / 2)))
            + (∑ i ∈ S, cc i * r i) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [hsum, hpb]
  unfold coordDefect
  have hcombine :
      (∑ j, ((∑ i ∈ S, cc i * p i j) * ((xl j + xu j) / 2)
              + (∑ i ∈ S, cc i * |p i j|) * ((xu j - xl j) / 2)))
        - (∑ j, ((∑ i ∈ S, cc i * p i j) * ((xl j + xu j) / 2)
              + |∑ i ∈ S, cc i * p i j| * ((xu j - xl j) / 2)))
      = ∑ j, ((∑ i ∈ S, cc i * |p i j|) - |∑ i ∈ S, cc i * p i j|)
              * ((xu j - xl j) / 2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  linarith

/-! ## 3.  Sign lemmas: triangle-defect nonnegativity, strictness, equality. -/

/-- The per-coordinate triangle defect is nonnegative (weighted triangle
inequality, `cc ≥ 0`). -/
theorem coord_term_nonneg {k : ℕ} (cc q : Fin k → ℚ) (hcc : ∀ i, 0 ≤ cc i)
    (S : Finset (Fin k)) :
    0 ≤ (∑ i ∈ S, cc i * |q i|) - |∑ i ∈ S, cc i * q i| := by
  have h1 : |∑ i ∈ S, cc i * q i| ≤ ∑ i ∈ S, |cc i * q i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ i ∈ S, |cc i * q i|) = ∑ i ∈ S, cc i * |q i| :=
    Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hcc i)]
  linarith

/-- Defect nonnegativity on every pattern. -/
theorem coordDefect_nonneg {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (xl xu : Fin n → ℚ) (hcc : ∀ i, 0 ≤ cc i) (hbox : ∀ j, xl j ≤ xu j)
    (S : Finset (Fin k)) :
    0 ≤ coordDefect cc p xl xu S := by
  unfold coordDefect
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (coord_term_nonneg cc (fun i => p i j) hcc S)
  have := hbox j
  linarith

/-- STRICT triangle inequality from one sign disagreement: if two members of `s`
have strictly opposite signs, `|∑ a| < ∑ |a|`. -/
theorem abs_sum_lt_sum_abs_of_mul_neg {k : ℕ} (a : Fin k → ℚ) (s : Finset (Fin k))
    {i₁ i₂ : Fin k} (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (hneg : a i₁ * a i₂ < 0) :
    |∑ i ∈ s, a i| < ∑ i ∈ s, |a i| := by
  have hwit : (∃ ip ∈ s, 0 < a ip) ∧ ∃ iq ∈ s, a iq < 0 := by
    rcases mul_neg_iff.mp hneg with ⟨hpos, hneg'⟩ | ⟨hneg', hpos⟩
    · exact ⟨⟨i₁, h₁, hpos⟩, ⟨i₂, h₂, hneg'⟩⟩
    · exact ⟨⟨i₂, h₂, hpos⟩, ⟨i₁, h₁, hneg'⟩⟩
  obtain ⟨⟨ip, hip, hppos⟩, ⟨iq, hiq, hqneg⟩⟩ := hwit
  rcases le_or_gt 0 (∑ i ∈ s, a i) with hT | hT
  · rw [abs_of_nonneg hT]
    have hpos : (0 : ℚ) < ∑ i ∈ s, (|a i| - a i) := by
      apply Finset.sum_pos'
      · intro i _
        have := le_abs_self (a i)
        linarith
      · refine ⟨iq, hiq, ?_⟩
        rw [abs_of_neg hqneg]
        linarith
    rw [Finset.sum_sub_distrib] at hpos
    linarith
  · rw [abs_of_neg hT]
    have hpos : (0 : ℚ) < ∑ i ∈ s, (|a i| + a i) := by
      apply Finset.sum_pos'
      · intro i _
        have := neg_abs_le (a i)
        linarith
      · refine ⟨ip, hip, ?_⟩
        rw [abs_of_pos hppos]
        linarith
    rw [Finset.sum_add_distrib] at hpos
    linarith

/-- Triangle EQUALITY under weak sign agreement: if all members of `s` are
(weakly) of one sign, `|∑ a| = ∑ |a|`. -/
theorem abs_sum_eq_sum_abs_of_sign_agree {k : ℕ} (a : Fin k → ℚ) (s : Finset (Fin k))
    (hagree : (∀ i ∈ s, 0 ≤ a i) ∨ (∀ i ∈ s, a i ≤ 0)) :
    |∑ i ∈ s, a i| = ∑ i ∈ s, |a i| := by
  rcases hagree with h | h
  · rw [abs_of_nonneg (Finset.sum_nonneg h)]
    exact Finset.sum_congr rfl fun i hi => (abs_of_nonneg (h i hi)).symm
  · rw [abs_of_nonpos (Finset.sum_nonpos h), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i hi => (abs_of_nonpos (h i hi)).symm

/-- **Per-coordinate criterion**: with strictly positive weights, the triangle
defect of a coordinate is strictly positive IFF two rows disagree in sign there.
This is the purely syntactic weight-sign test. -/
theorem coord_term_pos_iff {k : ℕ} (cc q : Fin k → ℚ) (hcc : ∀ i, 0 < cc i) :
    0 < (∑ i, cc i * |q i|) - |∑ i, cc i * q i| ↔ ∃ i₁ i₂, q i₁ * q i₂ < 0 := by
  have habs : (∑ i, |cc i * q i|) = ∑ i, cc i * |q i| :=
    Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (le_of_lt (hcc i))]
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have hagree : (∀ i ∈ Finset.univ, 0 ≤ cc i * q i)
        ∨ (∀ i ∈ Finset.univ, cc i * q i ≤ 0) := by
      by_cases hex : ∃ i, q i < 0
      · obtain ⟨i₀, hi₀⟩ := hex
        right
        intro i _
        have hqi : q i ≤ 0 := by
          by_contra hq
          push Not at hq
          exact absurd (hno i i₀) (not_le.mpr (mul_neg_of_pos_of_neg hq hi₀))
        exact mul_nonpos_iff.mpr (Or.inl ⟨le_of_lt (hcc i), hqi⟩)
      · push Not at hex
        left
        intro i _
        exact mul_nonneg (le_of_lt (hcc i)) (hex i)
    have heq := abs_sum_eq_sum_abs_of_sign_agree (fun i => cc i * q i)
      Finset.univ hagree
    rw [habs] at heq
    linarith
  · rintro ⟨i₁, i₂, hneg⟩
    have hprod : (cc i₁ * q i₁) * (cc i₂ * q i₂) < 0 := by
      have h3 := mul_neg_of_pos_of_neg (mul_pos (hcc i₁) (hcc i₂)) hneg
      calc (cc i₁ * q i₁) * (cc i₂ * q i₂)
          = (cc i₁ * cc i₂) * (q i₁ * q i₂) := by ring
        _ < 0 := h3
    have hlt := abs_sum_lt_sum_abs_of_mul_neg (fun i => cc i * q i) Finset.univ
      (Finset.mem_univ i₁) (Finset.mem_univ i₂) hprod
    rw [habs] at hlt
    linarith

/-! ## 4.  Assembly: the closed form. -/

/-- In the possibly-active regime, `relu` is the identity on the exact maxima. -/
theorem decoupled_eq_sum_uz {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hunst : ∀ i, 0 < uzExact p r xl xu i) :
    (∑ i, cc i * relu (uzExact p r xl xu i)) = ∑ i, cc i * uzExact p r xl xu i := by
  apply Finset.sum_congr rfl
  intro i _
  unfold relu
  rw [max_eq_right (le_of_lt (hunst i))]

/-- Per-pattern gap term: decoupled bound minus `patternBound_S` splits into the
off-pattern decoupled mass plus the pattern's coordinate defect. -/
theorem gap_term_eq {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ xu j) (hunst : ∀ i, 0 < uzExact p r xl xu i)
    (S : Finset (Fin k)) :
    (∑ i, cc i * relu (uzExact p r xl xu i)) - patternBound cc p r xl xu S
      = (∑ i ∈ Sᶜ, cc i * uzExact p r xl xu i) + coordDefect cc p xl xu S := by
  rw [decoupled_eq_sum_uz cc p r xl xu hunst]
  have hsplit : (∑ i ∈ S, cc i * uzExact p r xl xu i)
      + (∑ i ∈ Sᶜ, cc i * uzExact p r xl xu i)
      = ∑ i, cc i * uzExact p r xl xu i :=
    Finset.sum_add_sum_compl S _
  have hid := pattern_defect_identity cc p r xl xu hbox S
  linarith

/-- `sup'`/`inf'` duality over ℚ: a constant minus a finite sup is the inf of the
pointwise differences. -/
theorem const_sub_sup'_eq_inf' {β : Type*} (s : Finset β) (H : s.Nonempty)
    (c : ℚ) (f g : β → ℚ) (hfg : ∀ b ∈ s, c - f b = g b) :
    c - s.sup' H f = s.inf' H g := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro b hb
    rw [← hfg b hb]
    have h : f b ≤ s.sup' H f := Finset.le_sup' f hb
    linarith
  · obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup' H f
    rw [heq, hfg b hb]
    exact Finset.inf'_le g hb

/-- **`gap_closed_form` (main theorem 1).**  In the possibly-active regime
(`uzExact_i > 0`) with positive cut weights, the gap between the decoupled bound
(each neuron at its own exact box sup) and the closed-form joint-cut bound
(`sup'` of the `2^k` pattern bounds) equals the min over patterns of
[off-pattern decoupled mass + coordinate defect] — a closed form.

(`hcc` is carried to match the sealed conjecture statement; the equality itself
needs only `hbox` + `hunst`.) -/
theorem gap_closed_form {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < uzExact p r xl xu i) :
    (∑ i, cc i * relu (uzExact p r xl xu i))
      - (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
          (patternBound cc p r xl xu))
    = Finset.univ.powerset.inf' ⟨∅, Finset.empty_mem_powerset _⟩
        (fun S => (∑ i ∈ Sᶜ, cc i * uzExact p r xl xu i)
                  + coordDefect cc p xl xu S) := by
  apply const_sub_sup'_eq_inf'
  intro S _
  exact gap_term_eq cc p r xl xu hbox hunst S

/-! ## 5.  The iff: gap > 0 ⟺ a weight-syntactic sign test. -/

/-- The decoupled bound always dominates the joint-cut bound (sanity: the gap is
nonnegative). -/
theorem gap_nonneg {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < uzExact p r xl xu i) :
    0 ≤ (∑ i, cc i * relu (uzExact p r xl xu i))
          - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
              (patternBound cc p r xl xu) := by
  rw [gap_closed_form cc p r xl xu hcc hbox hunst]
  apply Finset.le_inf'
  intro S _
  have h1 : 0 ≤ ∑ i ∈ Sᶜ, cc i * uzExact p r xl xu i :=
    Finset.sum_nonneg fun i _ => le_of_lt (mul_pos (hcc i) (hunst i))
  have h2 := coordDefect_nonneg cc p xl xu (fun i => le_of_lt (hcc i)) hbox S
  linarith

/-- **`gap_pos_iff_sign_disagree` (main theorem 2, PHASE2 Pillar D's T-GAP).**
A multi-neuron value cut can strictly beat the decoupled relaxation on a box
domain IFF some non-degenerate input coordinate is pulled in opposite directions
by two group members — a purely syntactic weight-sign test, decidable by
inspection of the `p` matrix.

The iff is against the DECOUPLED / interval baseline (the `FacetCut.gapBdecoupled`
notion); no claim is made about the §7 chord-LP slack. -/
theorem gap_pos_iff_sign_disagree {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < uzExact p r xl xu i) :
    0 < (∑ i, cc i * relu (uzExact p r xl xu i))
          - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
              (patternBound cc p r xl xu)
      ↔ ∃ j, xl j < xu j ∧ ∃ i₁ i₂, p i₁ j * p i₂ j < 0 := by
  rw [gap_closed_form cc p r xl xu hcc hbox hunst, Finset.lt_inf'_iff]
  constructor
  · -- gap > 0 at EVERY pattern; at S = univ the off-pattern mass vanishes, so the
    -- defect itself is positive, which localizes to a sign-disagreeing coordinate.
    intro h
    have hu := h Finset.univ (Finset.mem_powerset_self _)
    rw [Finset.compl_univ, Finset.sum_empty, zero_add] at hu
    unfold coordDefect at hu
    have hex : ∃ j, (0 : ℚ) <
        ((∑ i, cc i * |p i j|) - |∑ i, cc i * p i j|) * ((xu j - xl j) / 2) := by
      by_contra hno
      push Not at hno
      have hle : (∑ j, ((∑ i, cc i * |p i j|) - |∑ i, cc i * p i j|)
          * ((xu j - xl j) / 2)) ≤ 0 :=
        Finset.sum_nonpos fun j _ => hno j
      linarith
    obtain ⟨j, hj⟩ := hex
    have htri : (0 : ℚ) ≤ (∑ i, cc i * |p i j|) - |∑ i, cc i * p i j| :=
      coord_term_nonneg cc (fun i => p i j) (fun i => le_of_lt (hcc i)) Finset.univ
    have hrad0 : (0 : ℚ) ≤ (xu j - xl j) / 2 := by
      have := hbox j
      linarith
    have hradpos : (0 : ℚ) < (xu j - xl j) / 2 := by
      rcases eq_or_lt_of_le hrad0 with he | hl
      · rw [← he] at hj
        simp at hj
      · exact hl
    have htpos : (0 : ℚ) < (∑ i, cc i * |p i j|) - |∑ i, cc i * p i j| := by
      rcases eq_or_lt_of_le htri with he | hl
      · rw [← he] at hj
        simp at hj
      · exact hl
    exact ⟨j, by linarith, (coord_term_pos_iff cc (fun i => p i j) hcc).mp htpos⟩
  · -- a sign-disagreeing coordinate makes EVERY pattern's term positive: proper
    -- patterns through their off-pattern decoupled mass, univ through its defect.
    rintro ⟨j, hjlt, i₁, i₂, hsign⟩ S hS
    by_cases hSu : S = Finset.univ
    · subst hSu
      rw [Finset.compl_univ, Finset.sum_empty, zero_add]
      unfold coordDefect
      apply Finset.sum_pos'
      · intro j' _
        apply mul_nonneg
          (coord_term_nonneg cc (fun i => p i j') (fun i => le_of_lt (hcc i)) _)
        have := hbox j'
        linarith
      · refine ⟨j, Finset.mem_univ j, mul_pos ?_ (by linarith)⟩
        exact (coord_term_pos_iff cc (fun i => p i j) hcc).mpr ⟨i₁, i₂, hsign⟩
    · have hexc : ∃ i0, i0 ∈ Sᶜ := by
        by_contra hno
        push Not at hno
        apply hSu
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        have hi := hno i
        rwa [Finset.mem_compl, not_not] at hi
      obtain ⟨i0, hi0⟩ := hexc
      have hpos : (0 : ℚ) < ∑ i ∈ Sᶜ, cc i * uzExact p r xl xu i :=
        Finset.sum_pos (fun i _ => mul_pos (hcc i) (hunst i)) ⟨i0, hi0⟩
      have hd := coordDefect_nonneg cc p xl xu (fun i => le_of_lt (hcc i)) hbox S
      linarith

/-- **The kernel-checked SKIP rule** (selection-rule corollary): the gap is zero —
the group provably CANNOT beat the decoupled bound — iff the group is
coordinate-sign-separable on every non-degenerate coordinate.  Contrapositive
form of the iff, packaged for cut selection: groups failing the sign test are
provably wasted cut premises. -/
theorem gap_eq_zero_iff_sign_separable {n k : ℕ} (cc : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < uzExact p r xl xu i) :
    (∑ i, cc i * relu (uzExact p r xl xu i))
        - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (patternBound cc p r xl xu) = 0
      ↔ ∀ j, xl j < xu j → ∀ i₁ i₂, 0 ≤ p i₁ j * p i₂ j := by
  have h0 := gap_nonneg cc p r xl xu hcc hbox hunst
  have hiff := gap_pos_iff_sign_disagree cc p r xl xu hcc hbox hunst
  constructor
  · intro h j hj i₁ i₂
    by_contra hneg
    push Not at hneg
    have hpos := hiff.mpr ⟨j, hj, i₁, i₂, hneg⟩
    linarith
  · intro h
    rcases eq_or_lt_of_le h0 with he | hlt
    · exact he.symm
    · obtain ⟨j, hj, i₁, i₂, hneg⟩ := hiff.mp hlt
      exact absurd hneg (not_lt.mpr (h j hj i₁ i₂))

/-! ## 6.  Secondary closed form (NO iff claimed): the chord-slack row assembles. -/

/-- The §7-style chord functional `∑_i d_i·(z_i(x) − lz_i)` (e.g. `d_i = cc_i·s_i`
for chord slopes `s_i`, offsets `lz_i`) is ONE assembled affine row of `x`. -/
theorem chord_slack_row_assemble {n k : ℕ} (d : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r lz : Fin k → ℚ) (x : Fin n → ℚ) :
    (∑ i, d i * (linVal (p i) x (r i) - lz i))
      = linVal (fun j => ∑ i, d i * p i j) x (∑ i, d i * (r i - lz i)) := by
  have hterm : ∀ i, linVal (p i) x (r i - lz i) = linVal (p i) x (r i) - lz i := by
    intro i
    unfold linVal
    ring
  calc (∑ i, d i * (linVal (p i) x (r i) - lz i))
      = (∑ i, d i * linVal (p i) x (r i - lz i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hterm i]
    _ = linVal (fun j => ∑ i, d i * p i j) x (∑ i, d i * (r i - lz i)) :=
        pattern_affine_assemble d p (fun i => r i - lz i) x Finset.univ

/-- **Secondary closed form**: the exact box maximum of the chord functional is
`boxMaxAffine` of its assembled row — sound at every box point and attained at a
box corner.  (Closed FORM only; no iff is claimed for the chord-LP slack.) -/
theorem chord_slack_closed_form {n k : ℕ} (d : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r lz : Fin k → ℚ) (xl xu : Fin n → ℚ) (hbox : ∀ j, xl j ≤ xu j) :
    (∀ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
        (∑ i, d i * (linVal (p i) x (r i) - lz i))
          ≤ boxMaxAffine (fun j => ∑ i, d i * p i j)
              (∑ i, d i * (r i - lz i)) xl xu)
    ∧ (∃ y, (∀ j, y j = xl j ∨ y j = xu j) ∧
        (∑ i, d i * (linVal (p i) y (r i) - lz i))
          = boxMaxAffine (fun j => ∑ i, d i * p i j)
              (∑ i, d i * (r i - lz i)) xl xu) := by
  constructor
  · intro x hx
    rw [chord_slack_row_assemble]
    exact le_boxMaxAffine _ _ xl xu x hx
  · obtain ⟨y, hy, heq⟩ := boxMaxAffine_attained (fun j => ∑ i, d i * p i j)
      (∑ i, d i * (r i - lz i)) xl xu hbox
    exact ⟨y, hy, by rw [chord_slack_row_assemble, heq]⟩

/-! ## 7.  Instance validation on the existing `FacetCut` k=2, n=1 gap instance
(`z1 = x`, `z2 = −x` on `[−1,1]`, unit weights): the sign test fires at
coordinate 0, recovering the strict coupling gap of `facet_gap_pos` through the
general theorem. -/

/-- Both exact pre-activation maxima of the `FacetCut` instance are `1 > 0`
(the possibly-active regime hypothesis holds). -/
theorem facetcut_unstable : ∀ i, 0 < uzExact gapW gapB gapXl gapXu i := by
  intro i
  unfold uzExact boxMaxAffine
  rw [Fin.sum_univ_one]
  fin_cases i
  · simp only [gapW, gapB, gapXl, gapXu, Matrix.cons_val_zero]
    rw [max_eq_right (by norm_num : (1 : ℚ) * (-1) ≤ 1 * 1)]
    norm_num
  · simp only [gapW, gapB, gapXl, gapXu, Matrix.cons_val_zero]
    rw [max_eq_left (by norm_num : (-1 : ℚ) * 1 ≤ -1 * -1)]
    norm_num

/-- On the `FacetCut` instance the gap is strictly positive — derived from the
general syntactic criterion (coordinate 0 is pulled in opposite directions:
`gapW 0 0 * gapW 1 0 = -1 < 0`), consistent with `facet_gap_pos`'s closed-form
gap `2 - 1 = 1 > 0`. -/
theorem facetcut_gap_pos :
    0 < (∑ i, gapCC i * relu (uzExact gapW gapB gapXl gapXu i))
          - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
              (patternBound gapCC gapW gapB gapXl gapXu) := by
  rw [gap_pos_iff_sign_disagree gapCC gapW gapB gapXl gapXu
      (fun i => by norm_num [gapCC])
      (fun j => by norm_num [gapXl, gapXu])
      facetcut_unstable]
  refine ⟨0, by norm_num [gapXl, gapXu], 0, 1, ?_⟩
  norm_num [gapW, Matrix.cons_val_zero]

#print axioms le_boxMaxAffine
#print axioms boxMaxAffine_attained
#print axioms boxMaxAffine_midrad
#print axioms jointCut_le_patternSup
#print axioms pattern_defect_identity
#print axioms coord_term_nonneg
#print axioms coordDefect_nonneg
#print axioms abs_sum_lt_sum_abs_of_mul_neg
#print axioms abs_sum_eq_sum_abs_of_sign_agree
#print axioms coord_term_pos_iff
#print axioms decoupled_eq_sum_uz
#print axioms gap_term_eq
#print axioms const_sub_sup'_eq_inf'
#print axioms gap_closed_form
#print axioms gap_nonneg
#print axioms gap_pos_iff_sign_disagree
#print axioms gap_eq_zero_iff_sign_separable
#print axioms chord_slack_row_assemble
#print axioms chord_slack_closed_form
#print axioms facetcut_unstable
#print axioms facetcut_gap_pos

end InventionWave1
end Crownproof
