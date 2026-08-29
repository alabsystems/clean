/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto4_bonferroni_lower_bound_card_biUnion`
(finite combinatorics: the FIRST BONFERRONI INEQUALITY for `Finset.card`).

────────────────────────────────────────────────────────────────────────────
THE THEOREM
────────────────────────────────────────────────────────────────────────────
For any finite family of finsets `A : ι → Finset α` indexed by `s : Finset ι`,
the cardinality of the union is bounded below by the union (degree-1) term minus
the pairwise-intersection (degree-2) correction:

    ∑ i ∈ s, #(A i)  ≤  #(s.biUnion A)  +  corr A s,

where `corr A s = ∑_{ {i,j} ⊆ s, i ≠ j } #(A i ∩ A j)` is the sum of pairwise
intersection cardinalities over UNORDERED off-diagonal index pairs (each pair
counted once, via `Finset.sym2`).  Rearranged over ℤ this is the textbook first
Bonferroni inequality / degree-2 lower-bound truncation of inclusion–exclusion:

    #(⋃ᵢ Aᵢ)  ≥  Σᵢ #Aᵢ  −  Σ_{i<j} #(Aᵢ ∩ Aⱼ).

It is stated additively over ℕ (`Σ #Aᵢ ≤ #⋃ + corr`) to avoid truncated ℕ
subtraction; the integer-subtraction form follows immediately.

WHY IT IS TRUE (and the proof skeleton)
  Induction on `s` with `Finset.cons_induction` (add one index `a ∉ s`):
  • `corr` cons law (`corr_cons`):  adding `a` adds exactly the new unordered
    pairs `{a, j}` for `j ∈ s`, so `corr A (cons a s) = corr A s + Σ_{j∈s} #(A a ∩ A j)`.
    Proved via `Finset.sym2_cons` + off-diagonal filtering (the new diagonal pair
    `{a,a}` is filtered out; every `{a,j}` with `j ∈ s` is genuinely off-diagonal
    because `a ∉ s`).
  • `#(A a ∪ U) + #(A a ∩ U) = #A a + #U`     (`card_union_add_card_inter`)
  • `#(A a ∩ U) = #(⋃_{j∈s} (A a ∩ A j)) ≤ Σ_{j∈s} #(A a ∩ A j)`
                                              (`inter_biUnion` + `card_biUnion_le`)
  • combine with the induction hypothesis by `omega`.

────────────────────────────────────────────────────────────────────────────
NOVELTY  (N1 — first formalization)
────────────────────────────────────────────────────────────────────────────
Mathlib has the FULL inclusion–exclusion EQUALITY
(`Finset.inclusion_exclusion_card_biUnion`,
`Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean`) and the degree-1
UPPER bound `Finset.card_biUnion_le` (`#(⋃ Aᵢ) ≤ Σ #Aᵢ`), but it does NOT have
the truncated Bonferroni BOUNDS.  In fact that very file lists them as open work:

    "## TODO
     * Prove that truncating the series alternatively gives an upper/lower bound
       to the true value."

A grep of `.lake/packages/mathlib/Mathlib` for `bonferroni` returns nothing;
searches for a pairwise-intersection correction term bounding `card_biUnion`
below (`sum_card .. ≤ card_biUnion .. + ..`, `sym2 .. inter`, `truncat`)
find only the unrelated Ahlswede–Zhang `truncatedSup`/`truncatedInf` and the
full-equality inclusion–exclusion.  This is therefore a genuinely new, stated,
kernel-checked result — the first Bonferroni inequality — not a restatement of
any single Mathlib lemma, and it discharges the degree-2 lower-bound half of an
explicitly-open Mathlib TODO.

Foundational: `#print axioms` of every declaration is ⊆ {propext,
Classical.choice, Quot.sound}.  NO `sorry`/`sorryAx`, NO `native_decide`, NO new
`axiom`.
-/
-- Minimal imports: `Finset.sym2`/`sym2_cons` (Data.Finset.Sym), `inter_biUnion`
-- (Data.Finset.Union), `card_union_add_card_inter` (Data.Finset.Card),
-- `card_biUnion_le` + `Finset.sum` (Algebra.BigOperators.Group.Finset.Basic).
-- NOT `import Mathlib` — a tight set keeps the graduation closure small.
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Crownproof.InventionWave5

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-! ## 1. The pairwise-intersection correction term.

`pairTerm A` sends an unordered index pair `s(i, j)` to `#(A i ∩ A j)`.  It is
well-defined on `Sym2 ι` because `A i ∩ A j = A j ∩ A i`. -/

/-- The symmetric pairwise-intersection cardinality, lifted to `Sym2 ι`. -/
noncomputable def pairTerm (A : ι → Finset α) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => #(A i ∩ A j), fun i j => by simp only []; rw [inter_comm]⟩

omit [DecidableEq ι] in
@[simp] theorem pairTerm_mk (A : ι → Finset α) (i j : ι) :
    pairTerm A s(i, j) = #(A i ∩ A j) := rfl

/-- The **Bonferroni correction term**: the sum of pairwise intersection
cardinalities over the UNORDERED off-diagonal index pairs of `s` (each pair
`{i, j}` with `i ≠ j` counted exactly once). -/
noncomputable def corr (A : ι → Finset α) (s : Finset ι) : ℕ :=
  ∑ p ∈ s.sym2.filter (fun p => ¬ p.IsDiag), pairTerm A p

/-- **Cons law for the correction term.**  Inserting a fresh index `a ∉ s` adds
exactly the new unordered pairs `{a, j}` for `j ∈ s`; the new diagonal pair
`{a, a}` is off-diagonal-filtered away, and every `{a, j}` (`j ∈ s`) is genuinely
off-diagonal since `a ∉ s`. -/
theorem corr_cons (A : ι → Finset α) (a : ι) (s : Finset ι) (ha : a ∉ s) :
    corr A (cons a s ha) = corr A s + ∑ j ∈ s, #(A a ∩ A j) := by
  unfold corr
  rw [sym2_cons, filter_disjUnion, sum_disjUnion, add_comm]
  congr 1
  -- map-part: pairs `s(a, b)` for `b ∈ cons a s`, off-diagonal-filtered.
  rw [sum_filter, sum_map, sum_cons]
  -- the `b = a` term is the diagonal `s(a,a)` ⟹ filtered out (contributes 0).
  rw [if_neg (by simp [Sym2.mkEmbedding_apply, Sym2.mk_isDiag_iff]), zero_add]
  -- the remaining `b ∈ s` terms: each `s(a,b)` is off-diagonal (`a ≠ b`).
  refine sum_congr rfl fun j hj => ?_
  have hne : a ≠ j := fun h => ha (h ▸ hj)
  rw [if_pos (by simp [Sym2.mkEmbedding_apply, Sym2.mk_isDiag_iff, hne])]
  simp [Sym2.mkEmbedding_apply, pairTerm_mk]

/-! ## 2. The first Bonferroni inequality. -/

/-- **First Bonferroni inequality for `Finset.card` (degree-2 lower bound).**
For any finite family `A : ι → Finset α` indexed by `s`,

    ∑ i ∈ s, #(A i)  ≤  #(s.biUnion A)  +  corr A s,

i.e. (over ℤ) `#(⋃ᵢ Aᵢ) ≥ Σᵢ #Aᵢ − Σ_{i<j} #(Aᵢ ∩ Aⱼ)`.

This is the degree-2 lower-bound truncation of inclusion–exclusion — the first
Bonferroni inequality — which Mathlib states only as an open TODO.  The proof is
by `cons`-induction: the union/intersection identity
`#(Aₐ ∪ U) + #(Aₐ ∩ U) = #Aₐ + #U`, with the intersection bounded by the new
pair contributions via `inter_biUnion`/`card_biUnion_le`, then combined with the
induction hypothesis and the `corr` cons law. -/
theorem auto4_bonferroni_lower_bound_card_biUnion (A : ι → Finset α) (s : Finset ι) :
    ∑ i ∈ s, #(A i) ≤ #(s.biUnion A) + corr A s := by
  induction s using Finset.cons_induction with
  | empty => simp [corr]
  | cons a s ha ih =>
    rw [sum_cons, corr_cons, cons_eq_insert, biUnion_insert]
    -- `#(Aₐ ∪ U) + #(Aₐ ∩ U) = #Aₐ + #U` where `U = s.biUnion A`.
    have hkey : #(A a ∪ s.biUnion A) + #(A a ∩ s.biUnion A) = #(A a) + #(s.biUnion A) :=
      card_union_add_card_inter _ _
    -- `#(Aₐ ∩ U) = #(⋃_{j∈s} (Aₐ ∩ Aⱼ)) ≤ Σ_{j∈s} #(Aₐ ∩ Aⱼ)`.
    have hinter : #(A a ∩ s.biUnion A) ≤ ∑ j ∈ s, #(A a ∩ A j) := by
      rw [inter_biUnion]; exact card_biUnion_le
    omega

/-! ## Trust-base check — every declaration reduces to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`,
NO `native_decide` / `Lean.ofReduceBool`. -/

#print axioms auto4_bonferroni_lower_bound_card_biUnion
#print axioms corr_cons

end Crownproof.InventionWave5
