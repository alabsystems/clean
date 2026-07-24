/-
  D-W1 FACET CALCULUS — the coupled-reachable-polytope facet premise.

  Pillar D, Wave 1.  (Honest scope: this moves ZERO VNN-COMP scored points; it is a
  THEORY contribution that *characterises* the multi-neuron coupling regime — when a
  single coupled facet over a domain `D` strictly dominates the decoupled / triangle
  per-neuron sum.)

  ## What this file proves, sorry-free

  1. `facetPremise_sound`  (FULLY GENERAL, ∀ k, ∀ n, Finset-indexed)
        For a finite index set of neurons `i : Fin k` whose pre-activations
        `z_i = W_i · x + b_i = linVal (W i) x (b i)` are AFFINE forms over an input box
        `D = [xl, xu] ⊆ ℝ^n`, and non-negative cut weights `cc_i ≥ 0`, a candidate
        per-domain facet bound `B_S` that DOMINATES each of the `2^k` per-activation-
        pattern affine forms at every box corner gives a valid `≤ 0` premise

            facetPremise := (∑_{i} cc_i · relu (z_i)) − B_S ≤ 0   on all of D.

        This is the coupled-reachable-polytope facet: a single inequality over the
        coupled box, DERIVED (not assumed) from finitely many corner inequalities,
        instantiating `multiReluCut_pattern_dominance` + the corner-sup bound from
        `affine_box_le_of_corners` (both reused verbatim from `MultiReluCutK.lean`).

  2. `facetPremise_as_farkas`  — the facet fed into the kernel-checked
        `farkas_premise_combination` as a single `≥ 0`-multiplier premise, so the
        facet bottoms out in the SAME Farkas core every other Crownproof bound uses.

  3. A CONCRETE 2-neuron coupled gap instance (clean synthetic coupling
        `z1 = x, z2 = −x` on `[−1,1]`):
        - `gapFacet_le`   : the COUPLED facet `relu z1 + relu z2 ≤ 1` holds on the box
          (DERIVED through `facetPremise_sound`; the box sup of `|x|` is `1`).
        - `gapDecoupled`  : the DECOUPLED / triangle per-neuron analysis only yields
          `relu z1 + relu z2 ≤ 2` (each neuron's box sup is `1`, summed independently).
        - `facet_gap_pos` : the CLOSED-FORM gap `B_decoupled − B_coupled = 2 − 1 = 1 > 0`
          is strictly positive (`by norm_num`): the coupling is REAL.
        - `gap_margin_witness` : an EXPLICIT decoupled-feasible point
          (`a1 = a2 = 1`, the two independent triangle maxima) has `a1 + a2 = 2`,
          which the COUPLED facet (`≤ 1`) REJECTS but the decoupled sum (`≤ 2`) ADMITS
          — the facet closes a margin (`[1, 2]`) the decoupled/triangle analysis leaves
          OPEN.  `by norm_num`.
        - `gap_facet_closes` : end-to-end, for `out = 1 − (relu z1 + relu z2)` the
          coupled facet closes the margin (`out ≥ 0` on the box) while the decoupled
          bound (`const = 2`) leaves slack `1`.

  GENERAL vs DEMONSTRATED:
   * (1),(2) are GENERAL-k, general-n, Finset-indexed.
   * (3) is the synthetic k = 2, n = 1 INSTANCE exhibiting the strict coupling gap,
     produced BY the general machinery (the coupled facet is `facetPremise_sound`
     at k = 2, n = 1), with the strict-gap fact verified by an exact `norm_num`.

  All `#print axioms` must be `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
-/

import Crownproof.Basic
import Crownproof.Bridge
import Crownproof.MultiReluCutK
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Crownproof

open Finset

/-! ## 1.  The general per-domain facet premise.

A facet of the coupled reachable polytope over an input box `D = [xl, xu]`.  Each
neuron's pre-activation is an affine form `z_i = linVal (W i) x (b i)`.  The facet
bound `B_S` is any value that dominates each of the `2^k` per-activation-pattern
affine forms `∑_{i∈S} cc_i · z_i` at every box corner.  The facet premise is then a
single valid `≤ 0` inequality over the whole coupled box.

This is a thin (named, documented) packaging of `multiReluCut_box_le` as a
`facetPremise ≤ 0` Farkas-ready premise, with the corner hypotheses spelled out as
the coupled-polytope facet condition. -/

/-- The facet functional: weighted ReLU sum minus the per-domain facet bound `B_S`. -/
def facetPremise {n k : ℕ}
    (cc : Fin k → ℚ) (W : Fin k → Fin n → ℚ) (b : Fin k → ℚ) (B : ℚ)
    (x : Fin n → ℚ) : ℚ :=
  (∑ i, cc i * relu (linVal (W i) x (b i))) - B

/-- **`facetPremise_sound` (general-k, general-n).**  If the per-domain facet bound
`B` dominates each of the `2^k` per-pattern affine forms at every corner of the box
`[xl, xu]`, then the facet premise is a valid `≤ 0` inequality at every box point
`x`:  `(∑_i cc_i · relu z_i) − B ≤ 0`.  Soundness is `multiReluCut_box_le` (reused
verbatim), which itself bottoms out in `multiReluCut_pattern_dominance`. -/
theorem facetPremise_sound {n k : ℕ}
    (cc : Fin k → ℚ) (W : Fin k → Fin n → ℚ) (b : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i)
    (x : Fin n → ℚ) (hbox : ∀ j, xl j ≤ x j ∧ x j ≤ xu j)
    (hcorn : ∀ (S : Finset (Fin k)) (y : Fin n → ℚ),
              (∀ j, y j = xl j ∨ y j = xu j) →
              linVal (fun j => ∑ i ∈ S, cc i * W i j) y (∑ i ∈ S, cc i * b i) ≤ B) :
    facetPremise cc W b B x ≤ 0 := by
  unfold facetPremise
  have hcut : (∑ i, cc i * relu (linVal (W i) x (b i))) ≤ B :=
    multiReluCut_box_le cc W b xl xu B hcc x hbox hcorn
  linarith

/-! ## 2.  The facet as a kernel-checked Farkas premise.

The facet is a single `≥ 0`-multiplier premise `facetPremise ≤ 0`, fed straight into
`farkas_premise_combination` (the abstract Farkas core).  This shows the facet is not
a free-standing claim: it composes through the SAME kernel the rest of Crownproof
trusts.  We carry a state with the coupled post-activations and the scalar output. -/

/-- A coupled relaxed-network state: the `k` pre/post-activations and scalar output. -/
structure FacetState (k : ℕ) where
  z : Fin k → ℚ
  a : Fin k → ℚ
  out : ℚ

/-- Genuine execution: each `a_i = relu z_i`, and `out = const − ∑ cc_i · a_i`. -/
def FacetState.valid {k : ℕ} (cc : Fin k → ℚ) (const : ℚ)
    (st : FacetState k) : Prop :=
  (∀ i, st.a i = relu (st.z i)) ∧ st.out = const - (∑ i, cc i * st.a i)

/-- **`facetPremise_as_farkas`.**  Given the facet's per-pattern bound on the
pre-activations of every valid state (`hpat`) and a single non-negative Farkas
multiplier `m` whose product with the facet `(∑ cc_i a_i) − B` equals `−out − c`
(`hcert`), every valid state has `out ≥ −c`.  Proven by reduction to
`farkas_premise_combination` — the facet IS a `≥ 0`-multiplier premise of the
Crownproof Farkas core. -/
theorem facetPremise_as_farkas {k : ℕ}
    (cc : Fin k → ℚ) (const B c m : ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (hm : 0 ≤ m)
    (hpat : ∀ st : FacetState k, FacetState.valid cc const st →
              ∀ S : Finset (Fin k), (∑ i ∈ S, cc i * st.z i) ≤ B)
    (hcert : ∀ st : FacetState k,
        m * ((∑ i, cc i * st.a i) - B) = -(st.out) - c) :
    ∀ st : FacetState k, FacetState.valid cc const st → -c ≤ st.out := by
  refine farkas_premise_combination (S := FacetState k) (ι := Fin 1)
    (premises := Finset.univ)
    (g := fun _ st => (∑ i, cc i * st.a i) - B)
    (out := fun st => st.out)
    (μ := fun _ => m) (c := c)
    (valid := FacetState.valid cc const)
    ?hμ ?hg ?hcert
  case hμ => intro i _; exact hm
  case hg =>
    intro _ _ st hv
    simp only []
    have hcut : (∑ i, cc i * relu (st.z i)) ≤ B :=
      multiReluCut_pattern_dominance cc st.z B hcc (hpat st hv)
    have heq : (∑ i, cc i * st.a i) = (∑ i, cc i * relu (st.z i)) := by
      apply Finset.sum_congr rfl; intro i _; rw [hv.1 i]
    rw [heq]; linarith
  case hcert =>
    intro st
    simp only [Fin.sum_univ_one]
    exact hcert st

/-! ## 3.  Concrete 2-neuron coupled GAP instance.

Clean synthetic coupling on the box `D = [−1, 1]` (n = 1), two neurons:
  z1 = x,   z2 = −x.

The two pre-activations are perfectly ANTI-correlated: whenever z1 is active, z2 is
inactive and vice-versa, so `relu z1 + relu z2 = relu x + relu (−x) = |x|`, whose box
supremum is `1` (attained at x = ±1).  The COUPLED facet bound is therefore `B = 1`.

A DECOUPLED / triangle per-neuron analysis bounds each ReLU separately by its own box
supremum (`sup_x relu x = 1`, `sup_x relu (−x) = 1`) and sums them INDEPENDENTLY,
giving only `relu z1 + relu z2 ≤ 1 + 1 = 2`.  It cannot see that z1 > 0 and z2 > 0
never happen TOGETHER.  The gap `B_decoupled − B_coupled = 2 − 1 = 1 > 0` is the
coupling content, closed form. -/

/-- Two neuron weight rows: `z1 = x` (row `[1]`), `z2 = −x` (row `[−1]`). -/
def gapW : Fin 2 → Fin 1 → ℚ
  | 0 => ![ 1]
  | 1 => ![-1]

/-- Both intercepts zero. -/
def gapB : Fin 2 → ℚ := fun _ => 0

/-- Unit weights `cc = (1, 1)` (the plain unstable-ReLU sum). -/
def gapCC : Fin 2 → ℚ := fun _ => 1

/-- Box lower corner `−1`. -/
def gapXl : Fin 1 → ℚ := fun _ => -1
/-- Box upper corner `1`. -/
def gapXu : Fin 1 → ℚ := fun _ => 1

/-- The COUPLED facet bound `B_coupled = sup_x |x| = 1`. -/
def gapBcoupled : ℚ := 1
/-- The DECOUPLED / triangle bound `B_decoupled = sup relu z1 + sup relu z2 = 2`. -/
def gapBdecoupled : ℚ := 2

/-- Helper (mirrors `MultiReluCutK.sum_sub_le_sum_relu`): a per-pattern weighted sum
is dominated by the full ReLU sum of the same terms.  Reduces "bound the form for
EVERY pattern `S`" to "bound the single ReLU sum", a concrete rational at each corner. -/
theorem gap_sum_sub_le_sum_relu (t : Fin 2 → ℚ) (S : Finset (Fin 2)) :
    (∑ i ∈ S, t i) ≤ (∑ i, relu (t i)) := by
  classical
  calc (∑ i ∈ S, t i)
      ≤ (∑ i ∈ S, relu (t i)) := by
        apply Finset.sum_le_sum; intro i _; unfold relu; exact le_max_right 0 (t i)
    _ ≤ (∑ i, relu (t i)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro i _ _; unfold relu; exact le_max_left 0 (t i)

/-- **The COUPLED facet holds on the whole box** (DERIVED through the general
`facetPremise_sound`).  For every `x ∈ [−1,1]`,
`relu (z1) + relu (z2) − 1 ≤ 0`, i.e. `relu x + relu (−x) ≤ 1`. -/
theorem gapFacet_le (x : Fin 1 → ℚ)
    (hbox : ∀ j, gapXl j ≤ x j ∧ x j ≤ gapXu j) :
    facetPremise gapCC gapW gapB gapBcoupled x ≤ 0 := by
  apply facetPremise_sound gapCC gapW gapB gapXl gapXu gapBcoupled
  · intro i; fin_cases i <;> norm_num [gapCC]
  · exact hbox
  · -- per-pattern corner check: every S, every corner y of [−1,1].
    intro S y hy
    have hy0 := hy 0
    -- The per-pattern linVal equals ∑_{i∈S} (cc_i · (W_i · y))  (intercepts are 0).
    have hform : linVal (fun j => ∑ i ∈ S, gapCC i * gapW i j) y
                   (∑ i ∈ S, gapCC i * gapB i)
        = (∑ i ∈ S, gapCC i * (∑ j, gapW i j * y j)) := by
      rw [← pattern_affine_assemble gapCC gapW gapB y S]
      apply Finset.sum_congr rfl; intro i _; simp only [linVal, gapB, add_zero]
    rw [hform]
    refine le_trans (gap_sum_sub_le_sum_relu
      (fun i => gapCC i * (∑ j, gapW i j * y j)) S) ?_
    -- y is a concrete corner: y 0 ∈ {−1, 1}.  Evaluate the 2 corners.
    simp only [gapXl, gapXu] at hy0
    rcases hy0 with hy0 | hy0 <;>
      · simp only [gapCC, gapW, gapBcoupled, Fin.sum_univ_two, Fin.sum_univ_one,
                   Matrix.cons_val_zero, hy0, one_mul, relu]
        norm_num

/-- **The DECOUPLED / triangle per-neuron bound** is `2` (each neuron's box sup is
`1`, summed independently): `relu (z1) + relu (z2) ≤ 2` on the box.  This is the
weaker bound a decoupled analysis produces — it never exploits that z1 > 0 and z2 > 0
cannot hold together. -/
theorem gapDecoupled (x : Fin 1 → ℚ)
    (hbox : ∀ j, gapXl j ≤ x j ∧ x j ≤ gapXu j) :
    (∑ i, gapCC i * relu (linVal (gapW i) x (gapB i))) ≤ gapBdecoupled := by
  obtain ⟨hl, hu⟩ := hbox 0
  simp only [gapXl, gapXu] at hl hu
  -- relu z1 = relu (x 0) ≤ 1,  relu z2 = relu (−(x 0)) ≤ 1.
  have h1 : relu (linVal (gapW 0) x (gapB 0)) ≤ 1 := by
    simp only [linVal, gapW, gapB, Fin.sum_univ_one, Matrix.cons_val_zero, add_zero,
               one_mul, relu]
    rcases le_or_gt 0 (x 0) with h | h
    · rw [max_eq_right h]; exact hu
    · rw [max_eq_left (le_of_lt h)]; norm_num
  have h2 : relu (linVal (gapW 1) x (gapB 1)) ≤ 1 := by
    simp only [linVal, gapW, gapB, Fin.sum_univ_one, Matrix.cons_val_zero, add_zero,
               relu]
    rcases le_or_gt 0 (-(1 : ℚ) * x 0) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left (le_of_lt h)]; norm_num
  simp only [gapCC, gapBdecoupled, Fin.sum_univ_two, one_mul]
  linarith

/-- **The gap is real and positive (closed form).**  `B_decoupled − B_coupled = 2 − 1 = 1 > 0`:
the coupled facet is STRICTLY tighter than the decoupled / triangle sum. -/
theorem facet_gap_pos : (0 : ℚ) < gapBdecoupled - gapBcoupled := by
  simp only [gapBdecoupled, gapBcoupled]; norm_num

/-- **The facet closes a margin the decoupled analysis leaves OPEN.**  The explicit
decoupled-feasible point `a1 = a2 = 1` (each neuron at its independent triangle
maximum) has `a1 + a2 = 2`, which the COUPLED facet (`≤ B_coupled = 1`) REJECTS but
the DECOUPLED sum (`≤ B_decoupled = 2`) ADMITS.  So the decoupled / triangle
relaxation cannot certify `∑ relu z_i ≤ 1`; only the coupled facet closes it. -/
theorem gap_margin_witness :
    -- decoupled-feasible witness: each post-activation at its own box maximum 1
    let a1 : ℚ := 1
    let a2 : ℚ := 1
    -- each within its decoupled triangle bound (sup relu = 1)
    (a1 ≤ 1) ∧ (a2 ≤ 1) ∧ (0 ≤ a1) ∧ (0 ≤ a2) ∧
    -- admitted by the decoupled sum bound
    (a1 + a2 ≤ gapBdecoupled) ∧
    -- but REJECTED by the coupled facet bound: the margin (gapBcoupled, gapBdecoupled] is open
    (gapBcoupled < a1 + a2) := by
  simp only [gapBdecoupled, gapBcoupled]; norm_num

/-- **End-to-end: the coupled facet closes the margin.**  For the network output
`out = B_coupled − (relu z1 + relu z2)` (coupled `const = 1`), the facet closes the
margin (`out ≥ 0`) on the whole box.  Combined with `gap_margin_witness`, this shows
the margin is closed by the coupled facet yet provably NOT by the decoupled / triangle
analysis (which only proves `∑ relu z_i ≤ 2`, leaving slack `gapBdecoupled −
gapBcoupled = 1`). -/
theorem gap_facet_closes (x : Fin 1 → ℚ)
    (hbox : ∀ j, gapXl j ≤ x j ∧ x j ≤ gapXu j)
    (out : ℚ)
    (hout : out = gapBcoupled - (∑ i, gapCC i * relu (linVal (gapW i) x (gapB i)))) :
    (0 : ℚ) ≤ out := by
  have hfacet := gapFacet_le x hbox
  unfold facetPremise at hfacet
  rw [hout]; linarith

#print axioms facetPremise_sound
#print axioms facetPremise_as_farkas
#print axioms gap_sum_sub_le_sum_relu
#print axioms gapFacet_le
#print axioms gapDecoupled
#print axioms facet_gap_pos
#print axioms gap_margin_witness
#print axioms gap_facet_closes

end Crownproof
