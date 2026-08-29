/-
  β-CROWN split-dual soundness + enclosure-intersection + mixed-leaf tree
  composition ("BetaSplit") — the soundness theory of the exact verifier stack
  used in the cifar100 hard-six campaign.  Everything over ℚ; abstract input
  type α for the domain.  All theorems must end with NO `sorry` and
  `#print axioms` ⊆ [propext, Classical.choice, Quot.sound].
-/

import Mathlib

namespace BetaSplit

/-! ## 1. Lagrangian split-dual soundness (the β-CROWN core fact).

A BaB subdomain is `D ∩ {x | ∀ j, s j * z j x ≥ 0}`: split constraints with
sign `s j ∈ {1, -1}` on pre-activations `z j`.  For ANY multipliers β j ≥ 0,
any lower bound `L` of the FOLDED objective `f x − Σ j, β j * s j * z j x`
over the WHOLE of `D` is a valid lower bound of `f` on the split subdomain
(because the folded correction is ≤ 0 there).  This is why any β ≥ 0 is sound
and the ascent needs no convergence. -/
theorem beta_split_dual_sound
    {α : Type*} {m : ℕ} (D : Set α) (f : α → ℚ)
    (z : Fin m → α → ℚ) (s : Fin m → ℚ) (β : Fin m → ℚ) (L : ℚ)
    (hβ : ∀ j, 0 ≤ β j)
    (hL : ∀ x ∈ D, L ≤ f x - (∑ j, β j * s j * z j x)) :
    ∀ x ∈ D, (∀ j, 0 ≤ s j * z j x) → L ≤ f x := by
  intro x hx hsplit
  have hS : 0 ≤ ∑ j, β j * s j * z j x := by
    apply Finset.sum_nonneg
    intro j _
    rw [mul_assoc]
    exact mul_nonneg (hβ j) (hsplit j)
  have := hL x hx
  linarith

/-! ## 2. Enclosure intersection soundness (the refinement-merge fact).

If two interval enclosures both contain a value, so does their intersection
taken coordinatewise as max of lowers / min of uppers.  Stated per-value. -/
theorem enclosure_intersect_sound
    (l₁ u₁ l₂ u₂ v : ℚ)
    (h₁ : l₁ ≤ v ∧ v ≤ u₁) (h₂ : l₂ ≤ v ∧ v ≤ u₂) :
    max l₁ l₂ ≤ v ∧ v ≤ min u₁ u₂ := by
  exact ⟨max_le h₁.1 h₂.1, le_min h₁.2 h₂.2⟩

/-! ## 3. Split-clamp strengthening of an enclosure.

On the subdomain where a split forces `0 ≤ z x` (active premise), a sound
enclosure `[l, u]` of `z` strengthens to `[max l 0, u]`; on an inactive
premise (`z x ≤ 0`) it strengthens to `[l, min u 0]`.  Both directions. -/
theorem clamp_active_sound
    {α : Type*} (D : Set α) (z : α → ℚ) (l u : ℚ)
    (henc : ∀ x ∈ D, l ≤ z x ∧ z x ≤ u) :
    ∀ x ∈ D, 0 ≤ z x → (max l 0 ≤ z x ∧ z x ≤ u) := by
  intro x hx hz
  exact ⟨max_le (henc x hx).1 hz, (henc x hx).2⟩

theorem clamp_inactive_sound
    {α : Type*} (D : Set α) (z : α → ℚ) (l u : ℚ)
    (henc : ∀ x ∈ D, l ≤ z x ∧ z x ≤ u) :
    ∀ x ∈ D, z x ≤ 0 → (l ≤ z x ∧ z x ≤ min u 0) := by
  intro x hx hz
  exact ⟨(henc x hx).1, le_min (henc x hx).2 hz⟩

/-! ## 4. Split-tree coverage with MIXED leaf certificates.

A binary split tree over a domain: each internal node splits on the sign of
some `z x`; the two children cover the parent (0 boundary in both).  We state
the recursion principle abstractly over an indexed family: if `D` is covered
by finitely many leaf regions `R i ⊆ D` (`∀ x ∈ D, ∃ i, x ∈ R i`) and each
leaf carries a certified bound `∀ x ∈ R i, c ≤ f x` — no matter HOW each leaf
was certified (CROWN/Farkas or a MIP pattern-tree) — then `c ≤ f x` on `D`.
This is the checker-side glue for a hard-six certificate whose leaves mix
bound families. -/
theorem mixed_leaf_cover_sound
    {α : Type*} {n : ℕ} (D : Set α) (R : Fin n → Set α) (f : α → ℚ) (c : ℚ)
    (hcover : ∀ x ∈ D, ∃ i, x ∈ R i)
    (hleaf : ∀ i, ∀ x ∈ R i, c ≤ f x) :
    ∀ x ∈ D, c ≤ f x := by
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact hleaf i x hi

/-! ## 5. The binary ReLU split covers the parent.

The two children of a ReLU split (active: `0 ≤ z x`; inactive: `z x ≤ 0`)
cover the parent domain — the union-cover fact that makes any branching
choice sound. -/
theorem relu_split_covers
    {α : Type*} (D : Set α) (z : α → ℚ) :
    ∀ x ∈ D, (0 ≤ z x) ∨ (z x ≤ 0) := by
  intro x _
  exact le_total 0 (z x)

/-! ## 6. End-to-end subdomain verdict.

Combining 1+5 down a path: if along a split path with signs `s j` the folded
bound `L ≥ 0` holds (hypothesis shape of theorem 1 with `L = 0` allowed via
`c`), the subdomain's margin is nonnegative — the exact statement a verified
BaB leaf cites.  Stated as the specialization of `beta_split_dual_sound`
to a nonneg bound. -/
theorem leaf_verified_of_folded_nonneg
    {α : Type*} {m : ℕ} (D : Set α) (f : α → ℚ)
    (z : Fin m → α → ℚ) (s : Fin m → ℚ) (β : Fin m → ℚ)
    (hβ : ∀ j, 0 ≤ β j)
    (hL : ∀ x ∈ D, 0 ≤ f x - (∑ j, β j * s j * z j x)) :
    ∀ x ∈ D, (∀ j, 0 ≤ s j * z j x) → 0 ≤ f x := by
  exact beta_split_dual_sound D f z s β 0 hβ hL

#print axioms beta_split_dual_sound
#print axioms enclosure_intersect_sound
#print axioms clamp_active_sound
#print axioms clamp_inactive_sound
#print axioms mixed_leaf_cover_sound
#print axioms relu_split_covers
#print axioms leaf_verified_of_folded_nonneg

end BetaSplit
