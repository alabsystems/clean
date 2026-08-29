/-
  MIP-verification certificate schema ("MipCert") — the soundness theory for
  verifying a neural-network subdomain by an exact big-M MIP over the last
  block(s), with a kernel-checkable certificate: an activation-pattern tree
  whose leaves carry Farkas (nonneg-combination) certificates.

  Motivation: a branch-and-bound verifier leaves "pinned" subdomains whose
  relaxed bound is negative but whose EXACT optimum over the last block(s) may
  be ≥ 0.  A MIP solver proves min ≥ 0, but its word is not a proof.  The
  checkable object is: (1) the reachable set is CONTAINED in the MIP feasible
  set (big-M ReLU feasibility, given valid pre-activation bounds), and (2) a
  complete enumeration of activation patterns, each leaf certified ≥ 0 by an
  explicit Farkas combination of the leaf's linear constraints.  Everything
  over ℚ.  All theorems must end with NO `sorry`, and `#print axioms` must be
  a subset of [propext, Classical.choice, Quot.sound].
-/

import Mathlib

namespace MipCert

/-- ReLU over ℚ. -/
def relu (x : ℚ) : ℚ := max x 0

/-! ## 1. Big-M feasibility containment (soundness direction).

Given valid bounds `l ≤ z ≤ u` on a pre-activation, the exact point
`(z, relu z)` is feasible for the big-M constraint block with the indicator
chosen as `δ = 1` iff `0 ≤ z` (δ here is ℚ-valued but constrained to {0,1}).
The four constraints (standard big-M ReLU encoding with M⁺ = u, M⁻ = −l):
  y ≥ z,  y ≥ 0,  y ≤ z − l·(1 − δ),  y ≤ u·δ.
This is the CONTAINMENT direction a verifier needs: every reachable point is
MIP-feasible, hence MIP-min ≤ true min, hence MIP-min ≥ 0 ⇒ true min ≥ 0. -/
theorem bigM_relu_feasible
    (l u z : ℚ) (hl : l ≤ z) (hu : z ≤ u) :
    ∃ δ : ℚ, (δ = 0 ∨ δ = 1)
      ∧ relu z ≥ z
      ∧ relu z ≥ 0
      ∧ relu z ≤ z - l * (1 - δ)
      ∧ relu z ≤ u * δ := by
  by_cases h : 0 ≤ z
  · refine ⟨1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp only [relu, max_eq_left h, mul_one, sub_self, mul_zero, sub_zero]
    · exact le_refl _
    · exact h
    · exact le_refl _
    · exact hu
  · push Not at h
    refine ⟨0, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp only [relu, max_eq_right (le_of_lt h), mul_zero, sub_zero, mul_one]
    · exact le_of_lt h
    · exact le_refl _
    · linarith
    · exact le_refl _

/-! ## 2. Pattern-tree coverage.

For a vector of `k` pre-activations, every point picks the activation pattern
`S = {i | 0 ≤ z i}`; the per-pattern linear leaf region (z i ≥ 0 for i ∈ S,
z i ≤ 0 for i ∉ S, y i = z i on S, y i = 0 off S) contains `(z, relu ∘ z)`.
So a family of leaf certificates covering ALL patterns covers the reachable
set. -/
theorem pattern_leaf_membership
    {k : ℕ} (z : Fin k → ℚ) :
    ∃ S : Finset (Fin k),
      (∀ i ∈ S, 0 ≤ z i)
      ∧ (∀ i ∉ S, z i ≤ 0)
      ∧ (∀ i ∈ S, relu (z i) = z i)
      ∧ (∀ i ∉ S, relu (z i) = 0) := by
  refine ⟨Finset.univ.filter (fun i => 0 ≤ z i), ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    exact le_of_lt hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact max_eq_left hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    exact max_eq_right (le_of_lt hi)

/-! ## 3. Farkas leaf certification.

A leaf is a finite family of linear inequalities `g j x ≤ 0` (over any input
type) together with an affine objective `f`.  A Farkas certificate is a
nonnegative combination `lam` with  f x + Σ j, lam j * g j x ≥ c  for all x
AS AN ALGEBRAIC IDENTITY hypothesis (`hid`), which the kernel can check by
normalization on concrete data; then every leaf-feasible x has f x ≥ c. -/
theorem farkas_leaf_bound
    {α : Type*} {m : ℕ} (f : α → ℚ) (g : Fin m → α → ℚ)
    (lam : Fin m → ℚ) (c : ℚ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hid : ∀ x, f x + (∑ j, lam j * g j x) ≥ c) :
    ∀ x, (∀ j, g j x ≤ 0) → f x ≥ c := by
  intro x hx
  have hsum : (∑ j, lam j * g j x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hlam j) (hx j)
  have := hid x
  linarith

/-! ## 4. End-to-end: pattern-tree MIP certificate.

Combine 2 + 3: the margin `f` factors through pre-activations `z i x` and
post-activations `relu (z i x)`.  Suppose for EVERY pattern `S` we have a
Farkas certificate for the leaf "z i x ≥ 0 (i ∈ S), z i x ≤ 0 (i ∉ S)" that
lower-bounds the PATTERN-SPECIALIZED margin `fS` (= f with `relu (z i)`
replaced by `z i` on `S` and `0` off `S`) by `c ≥ 0`... rather than fixing a
concrete factoring, we state the coverage principle abstractly:

If for every pattern `S : Finset (Fin k)` there is a bound
`hS : ∀ x ∈ D, (∀ i ∈ S, 0 ≤ z i x) → (∀ i ∉ S, z i x ≤ 0) → c ≤ F x`,
then `c ≤ F x` for every `x ∈ D`.  (Each x lives in the leaf of its own
activation pattern.)  This is the checker-side recursion for the certificate
tree; leaves are discharged by `farkas_leaf_bound`. -/
theorem pattern_tree_cover
    {α : Type*} {k : ℕ} (D : Set α) (z : Fin k → α → ℚ) (F : α → ℚ) (c : ℚ)
    (hS : ∀ S : Finset (Fin k), ∀ x ∈ D,
      (∀ i ∈ S, 0 ≤ z i x) → (∀ i ∉ S, z i x ≤ 0) → c ≤ F x) :
    ∀ x ∈ D, c ≤ F x := by
  intro x hx
  apply hS (Finset.univ.filter (fun i => 0 ≤ z i x)) x hx
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    exact le_of_lt hi

/-! ## 5. Verification transfer.

If the margin function `M` agrees on `D` with a function `F` proven ≥ 0 by the
pattern tree (agreement = the ReLU factorization identity, checkable per
instance), then the property "M ≥ 0 on D" — i.e. the subdomain is VERIFIED —
holds.  Stated as a trivial but load-bearing transfer lemma so the certificate
pipeline has a single citation point. -/
theorem verified_of_pattern_tree
    {α : Type*} (D : Set α) (M F : α → ℚ)
    (hagree : ∀ x ∈ D, M x = F x)
    (hF : ∀ x ∈ D, 0 ≤ F x) :
    ∀ x ∈ D, 0 ≤ M x := by
  intro x hx
  rw [hagree x hx]
  exact hF x hx

/-! ## 6. Big-M leaf tightening under valid bounds (the "M is safe" lemma).

In the big-M encoding the constraint `y ≤ u * δ` with `δ = 0` forces `y ≤ 0`,
and with `δ = 1` gives `y ≤ u` — combined with `y ≥ z` and `y ≥ 0` this pins
`y = relu z` at pattern leaves PROVIDED the bounds are valid (`l ≤ z ≤ u`).
Concretely: on the active leaf (δ = 1, z ≥ 0), the constraints force
`z ≤ y ∧ y ≤ z - l·0 = z`... no: with δ = 1 the upper constraints are
`y ≤ z - 0 = z` and `y ≤ u`, and lower `y ≥ z, y ≥ 0` — so `y = z = relu z`.
On the inactive leaf (δ = 0, z ≤ 0): `y ≤ z - l ≥ 0`-side and `y ≤ 0`,
`y ≥ 0` — so `y = 0 = relu z`.  State both. -/
theorem bigM_leaf_pins_active
    (l u z y : ℚ) (hz : 0 ≤ z)
    (h1 : y ≥ z) (h3 : y ≤ z - l * (1 - 1)) :
    y = z := by
  simp only [sub_self, mul_zero, sub_zero] at h3
  linarith

theorem bigM_leaf_pins_inactive
    (u z y : ℚ)
    (h2 : y ≥ 0) (h4 : y ≤ u * 0) :
    y = 0 := by
  simp only [mul_zero] at h4
  linarith

#print axioms bigM_relu_feasible
#print axioms pattern_leaf_membership
#print axioms farkas_leaf_bound
#print axioms pattern_tree_cover
#print axioms verified_of_pattern_tree
#print axioms bigM_leaf_pins_active
#print axioms bigM_leaf_pins_inactive

end MipCert
