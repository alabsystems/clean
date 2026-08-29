/-
  Split-conditioned k-ReLU cut soundness + Lagrangian cut-fold injection
  ("Certified Cut-CROWN") — the theory package for injecting kernel-checked
  multi-neuron cuts, STRENGTHENED by branch-and-bound split premises, into a
  CROWN/β-CROWN-style GPU backward pass as `λ ≥ 0` dual multipliers.

  Context (already proven elsewhere, restated here self-contained):
  a k-ReLU cut `∑ i, cc i * relu (z i) ≤ B` is valid on a box when B dominates
  the per-activation-pattern affine forms at box corners (pattern dominance +
  corner derivation).  THIS file adds the two missing pieces:

  (1) SPLIT-CONDITIONED pattern dominance (`multiReluCut_split_pattern_dominance`,
      `multiReluCut_split_box_le`): on a BaB subdomain where split constraints
      force a subset `Act` of the k neurons active (`0 ≤ z i`) and a subset
      `Inact` inactive (`z i ≤ 0`), the joint bound `B` need only dominate the
      per-pattern forms for patterns `S` CONSISTENT with the splits
      (`Act ⊆ S` and `S ∩ Inact` contributes nothing).  With fewer patterns the
      derived `B` is (weakly) tighter — this is the BICCOS-style "implied cut
      strengthening", here PROVED rather than trusted.

      Boundary care: `Inact` carries `z i ≤ 0` (so `relu (z i) = 0`; a term with
      `z i = 0` contributes `cc i * 0 = 0` and may be dropped from the pattern
      sum).  The active set in the proof is `A = univ.filter (0 ≤ z ·)`;
      note `A ⊇ Act`, and `A ∩ Inact` only contains indices with `z i = 0`,
      whose pattern-sum terms vanish, so the hypothesis at `S = A \ Inact`
      suffices.

  (2) LAGRANGIAN CUT-FOLD soundness (`cut_fold_lower_bound`,
      `cuts_fold_lower_bound`): if each cut `g j x ≤ 0` holds pointwise on the
      (sub)domain `D` and `lam j ≥ 0`, then any `L` that lower-bounds the FOLDED
      objective `f x + ∑ j, lam j * g j x` on `D` lower-bounds `f` on `D`.
      This is the exact justification for adding `λᵀ·cut` terms to the CROWN
      backward coefficients: the backward bounds the folded objective, the
      theorem transfers the bound to the true objective.

  (3) End-to-end composition (`cutCrown_subdomain_sound`): on a box, with affine
      pre-activations, split premises, a pattern-restricted corner-derived `B`,
      and a backward-computed lower bound `L` of the folded objective, conclude
      `L ≤ f x` for every `x` in the box satisfying the split premises.

  Everything is over ℚ.  All theorems must end with NO `sorry` and
  `#print axioms` ⊆ [propext, Classical.choice, Quot.sound].
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Insert
import Mathlib
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace CutCrown

open Finset

/-- ReLU over ℚ. -/
def relu (x : ℚ) : ℚ := max x 0

/-- An affine functional of the box input. -/
def linVal {n : ℕ} (w : Fin n → ℚ) (x : Fin n → ℚ) (r : ℚ) : ℚ :=
  (∑ j, w j * x j) + r

/-- Membership of `x` in the axis-aligned box `[xl, xu]`. -/
def inBox {n : ℕ} (xl xu x : Fin n → ℚ) : Prop :=
  ∀ j, xl j ≤ x j ∧ x j ≤ xu j

/-! ## 1. Split-conditioned pattern dominance.

On a subdomain where split premises force `Act` active (`0 ≤ z i`) and `Inact`
inactive (`z i ≤ 0`), the joint bound `B` need only dominate per-pattern sums for
patterns consistent with the splits: `Act ⊆ S` and `S` disjoint from `Inact`. -/

theorem multiReluCut_split_pattern_dominance
    {k : ℕ} (cc z : Fin k → ℚ) (B : ℚ)
    (Act Inact : Finset (Fin k))
    (hdisj : Disjoint Act Inact)
    (hact : ∀ i ∈ Act, 0 ≤ z i)
    (hinact : ∀ i ∈ Inact, z i ≤ 0)
    (hcc : ∀ i, 0 ≤ cc i)
    (hpat : ∀ S : Finset (Fin k), Act ⊆ S → Disjoint S Inact →
      (∑ i ∈ S, cc i * z i) ≤ B) :
    (∑ i, cc i * relu (z i)) ≤ B := by
  -- Let $A = \{i \in \text{Fin } k \mid 0 \leq z_i\}$.
  set A : Finset (Fin k) := Finset.univ.filter (fun i => 0 ≤ z i);
  -- The full sum ∑ i, cc i * relu (z i) equals ∑ i ∈ A, cc i * z i.
  have hsum_A : ∑ i, cc i * relu (z i) = ∑ i ∈ A, cc i * z i := by
    rw [ Finset.sum_filter, ← Finset.sum_congr rfl ] ; intros ; unfold relu ; split_ifs <;> simp_all +decide [ le_of_lt ] ;
  -- Let $S = A \setminus \text{Inact}$.
  set S : Finset (Fin k) := A \ Inact;
  refine le_trans ?_ ( hpat S ?_ ?_ );
  · rw [ hsum_A, ← Finset.sum_sdiff <| Finset.subset_iff.mpr <| show S ⊆ A from fun x hx => by aesop ];
    simp +zetaDelta at *;
    exact Finset.sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos ( hcc i ) ( hinact i ( Finset.mem_of_mem_inter_right hi ) );
  · exact fun i hi => Finset.mem_sdiff.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hact i hi ⟩, fun hi' => Finset.disjoint_left.mp hdisj hi hi' ⟩;
  · exact Finset.sdiff_disjoint

/-! ## 2. Split-conditioned corner derivation.

Pre-activations are affine in the box input: `z i = linVal (w i) x (r i)`.
If `B` dominates the pattern sums for every SPLIT-CONSISTENT pattern at every
box corner (corners: each coordinate at `xl j` or `xu j`), then the cut
`∑ cc i * relu (z i x) ≤ B` holds for every `x` in the box that satisfies the
split premises.  (Hint: an affine functional attains its box max at a corner —
prove via induction on the coordinates, updating one coordinate at a time; the
pattern sum `∑_{i∈S} cc i * (linVal (w i) x (r i))` is itself affine in `x` with
weights `fun j => ∑_{i∈S} cc i * w i j` and offset `∑_{i∈S} cc i * r i`.) -/

theorem multiReluCut_split_box_le
    {n k : ℕ} (cc : Fin k → ℚ) (w : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (B : ℚ)
    (Act Inact : Finset (Fin k))
    (hdisj : Disjoint Act Inact)
    (hcc : ∀ i, 0 ≤ cc i)
    (hbox : ∀ j, xl j ≤ xu j)
    (hcorner : ∀ S : Finset (Fin k), Act ⊆ S → Disjoint S Inact →
      ∀ c : Fin n → Bool,
        (∑ i ∈ S, cc i * linVal (w i) (fun j => if c j then xu j else xl j) (r i)) ≤ B) :
    ∀ x : Fin n → ℚ, inBox xl xu x →
      (∀ i ∈ Act, 0 ≤ linVal (w i) x (r i)) →
      (∀ i ∈ Inact, linVal (w i) x (r i) ≤ 0) →
      (∑ i, cc i * relu (linVal (w i) x (r i))) ≤ B := by
  intro x hx hact hinact;
  apply multiReluCut_split_pattern_dominance cc (fun i => linVal (w i) x (r i)) B Act Inact hdisj hact hinact hcc;
  intro S hS₁ hS₂;
  -- By the key lemma (affine box max at corner), we have that $\sum_{i \in S} cc_i \cdot \text{linVal}(w_i, x, r_i) \leq \max_{c \in \{0,1\}^n} \sum_{i \in S} cc_i \cdot \text{linVal}(w_i, c, r_i)$.
  have h_affine_max : ∑ i ∈ S, cc i * linVal (w i) x (r i) ≤ ∑ j, (∑ i ∈ S, cc i * w i j) * (if (∑ i ∈ S, cc i * w i j) ≥ 0 then xu j else xl j) + ∑ i ∈ S, cc i * r i := by
    have h_affine_max : ∀ j, (∑ i ∈ S, cc i * w i j) * x j ≤ (∑ i ∈ S, cc i * w i j) * (if (∑ i ∈ S, cc i * w i j) ≥ 0 then xu j else xl j) := by
      intro j; split_ifs <;> nlinarith [ hx j, hbox j ] ;
    convert add_le_add_right ( Finset.sum_le_sum fun j _ => h_affine_max j ) ( ∑ i ∈ S, cc i * r i ) using 1;
    any_goals exact Finset.univ;
    · simp +decide [ linVal, Finset.sum_add_distrib, mul_add, Finset.mul_sum _ _ _, Finset.sum_mul ];
      rw [ add_comm, Finset.sum_comm ] ; simp +decide only [mul_assoc];
    · ring;
  refine le_trans h_affine_max ?_;
  convert hcorner S hS₁ hS₂ ( fun j => if ( ∑ i ∈ S, cc i * w i j ) ≥ 0 then Bool.true else Bool.false ) using 1;
  simp +decide [ linVal, Finset.sum_add_distrib, mul_add, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ Finset.sum_comm ] ; congr ; ext ; split_ifs <;> simp +decide [ *, mul_assoc ] ;

/-! ## 3. Lagrangian cut-fold: one cut. -/

theorem cut_fold_lower_bound
    {α : Type*} (D : Set α) (f g : α → ℚ) (lam L : ℚ)
    (hlam : 0 ≤ lam)
    (hcut : ∀ x ∈ D, g x ≤ 0)
    (hLB : ∀ x ∈ D, L ≤ f x + lam * g x) :
    ∀ x ∈ D, L ≤ f x := by
  exact fun x hx => le_trans ( hLB x hx ) ( add_le_of_nonpos_right ( mul_nonpos_of_nonneg_of_nonpos hlam ( hcut x hx ) ) )

/-! ## 4. Lagrangian cut-fold: m cuts. -/

theorem cuts_fold_lower_bound
    {α : Type*} {m : ℕ} (D : Set α) (f : α → ℚ) (g : Fin m → α → ℚ)
    (lam : Fin m → ℚ) (L : ℚ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hcut : ∀ j, ∀ x ∈ D, g j x ≤ 0)
    (hLB : ∀ x ∈ D, L ≤ f x + ∑ j, lam j * g j x) :
    ∀ x ∈ D, L ≤ f x := by
  exact fun x hx => le_trans ( hLB x hx ) ( add_le_of_nonpos_right ( Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos ( hlam j ) ( hcut j x hx ) ) )

/-! ## 5. End-to-end: certified cut-CROWN on a split subdomain.

`f` is the verification objective (margin).  The GPU backward computes `L`, a
lower bound of the FOLDED objective `f x + ∑ j, lam j * (cutSum j x - Bcut j)`
over the whole box (folding the cut's linear pattern pieces into the backward
coefficients).  Each cut `j` is a k-ReLU cut valid on the split subdomain by
(2).  Conclude `L` lower-bounds `f` on the subdomain.  This is the statement the
verifier cites per subdomain. -/

theorem cutCrown_subdomain_sound
    {n m : ℕ} (xl xu : Fin n → ℚ)
    (P : (Fin n → ℚ) → Prop)                    -- split premises (halfspaces)
    (f : (Fin n → ℚ) → ℚ)                        -- true objective
    (cutSum : Fin m → (Fin n → ℚ) → ℚ)           -- each cut's ReLU sum
    (Bcut : Fin m → ℚ) (lam : Fin m → ℚ) (L : ℚ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hcut : ∀ j, ∀ x : Fin n → ℚ, inBox xl xu x → P x → cutSum j x ≤ Bcut j)
    (hLB : ∀ x : Fin n → ℚ, inBox xl xu x → P x →
      L ≤ f x + ∑ j, lam j * (cutSum j x - Bcut j)) :
    ∀ x : Fin n → ℚ, inBox xl xu x → P x → L ≤ f x := by
  exact fun x hx hx' => le_trans ( hLB x hx hx' ) ( add_le_of_nonpos_right <| Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos ( hlam j ) <| sub_nonpos_of_le <| hcut j x hx hx' )

/-! ## 6. Strict strengthening witness (k = 2, one split premise).

Concrete demonstration that the split-conditioned cut is STRICTLY tighter than
any bound valid unconditionally on the box.  Take the box `x ∈ [-1, 1]` with
pre-activations `z 0 = x` and `z 1 = -x - 1/2`, weights `cc = (1, 1)`:

  (a) UNDER the split premise `z 1 ≥ 0` (i.e. `x ≤ -1/2`), the ReLU sum is
      bounded by `1/2` on the box: `relu x = 0` there and
      `relu (-x - 1/2) = -x - 1/2 ≤ 1/2`.
  (b) `1/2` is NOT a valid unconditional bound: at `x = 1` the ReLU sum is
      `relu 1 + relu (-3/2) = 1 > 1/2`.

So the split premise strictly tightens the best achievable cut constant. -/

theorem split_strengthening_strict :
    (∀ x : ℚ, -1 ≤ x → x ≤ 1 → 0 ≤ -x - 1/2 →
       relu x + relu (-x - 1/2) ≤ 1/2)
    ∧ (∃ x : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ ¬ (relu x + relu (-x - 1/2) ≤ 1/2)) := by
  constructor;
  · unfold relu; intro x hx₁ hx₂ hx₃; rw [ max_def, max_def ] ; split_ifs <;> linarith;
  · exact ⟨ 1, by norm_num, by norm_num, by unfold relu; norm_num ⟩

#print axioms multiReluCut_split_pattern_dominance
#print axioms multiReluCut_split_box_le
#print axioms cut_fold_lower_bound
#print axioms cuts_fold_lower_bound
#print axioms cutCrown_subdomain_sound
#print axioms split_strengthening_strict

end CutCrown
