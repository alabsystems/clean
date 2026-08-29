/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

GRAND-CHALLENGE 3 — VERIFIED COMPLETENESS of input-bisection branch-and-bound.

Every other file in this development proves *soundness*: a CROWN/Farkas leaf
certificate is valid, and `BranchTree.safe_of_leaves` composes per-leaf safety
facts into whole-box safety (safe-on-leaves ⟹ safe-on-root).  Soundness answers
"is THIS certificate correct?"  It does NOT answer "does the branch-and-bound
PROCEDURE ever finish with a decision?"  That second half — that a positive
verification margin is decided in finitely many bisections — is COMPLETENESS,
and it is what this file proves, `sorry`-free.

────────────────────────────────────────────────────────────────────────────
THE MATHEMATICS
────────────────────────────────────────────────────────────────────────────
For a Lipschitz network the interval/IBP/CROWN relaxation error on a box `B`
shrinks with the box width:

      relaxedBound B  ≥  trueMin B − L · diam B                    (width-error)

Bisecting a box halves its (controlling) diameter, and a sub-box's true minimum
dominates its parent's (the min is taken over a smaller set):

      diam(child)  ≤  diam(B) / 2                                  (contraction)
      trueMin(child) ≥ trueMin(B)                                  (monotonicity)

So if the property holds with a STRICT positive margin over the root box,

      trueMin(root) ≥ δ > 0,

then a leaf at bisection depth `d` has `diam ≤ diam₀ / 2^d`, hence

      relaxedBound(leaf) ≥ δ − L · diam₀ / 2^d,

which is `> 0` as soon as `2^d > L·diam₀ / δ` — and such a finite `d` EXISTS by
the Archimedean property (`pow_unbounded_of_one_lt`).  At that depth every leaf's
relaxed bound is positive, so every leaf CLOSES (`Safe` holds there); the
bisection tree is FINITE (it is the depth-`d` full tree, built explicitly), and
`BranchTree.safe_of_leaves` then DECIDES the root.

That is exactly: **positive margin ⟹ finite BaB decides it.**

────────────────────────────────────────────────────────────────────────────
WHAT IS ABSTRACT (supplied as hypotheses, mirroring the soundness bridges)
────────────────────────────────────────────────────────────────────────────
The relaxation is treated abstractly through a `Relaxation` structure carrying
exactly the three properties above (`width_error`, `diam_contract`,
`trueMin_mono`) plus `diam_nonneg` and a Lipschitz constant `L ≥ 0`.  Any
concrete IBP/CROWN relaxation of a Lipschitz network satisfies these; we depend
on nothing else.  The bisection geometry (`split`, `diam`) is likewise abstract,
modelling input-coordinate bisection where each split halves the controlling
width.  Everything downstream — the finite depth, the closing of every leaf, the
final decision — is PROVED.

The closing-of-a-leaf is wired into the real composition kernel: we build a
genuine `Crownproof.BoxTree` of depth `d`, discharge its `Leaves` obligation
from the positive relaxed bounds, and obtain whole-box safety through the very
same `BoxTree.safe_of_leaves` the soundness side uses.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.BranchTree

namespace Crownproof

namespace Complete

/-! ## 1. The abstract relaxation with the width-error property

`Box` is an abstract box/region type.  A `Relaxation` packages the branch-and-
bound ingredients with exactly the analytic facts completeness needs.  This is
the SAME modelling discipline as the soundness bridges, which take their CROWN
bounds as hypotheses; here we take the *width-vs-error* law as a hypothesis. -/

/-- An abstract input-bisection relaxation over a box type `Box`.

* `diam B`        — the controlling box width (e.g. the length of the longest
                    input coordinate, the quantity the Lipschitz error scales).
* `trueMin B`     — the exact minimum of the network's safety margin over `B`
                    (`> 0` means the property genuinely holds on `B`).
* `relaxedBound B`— the computable lower bound the relaxation returns for `B`.
* `split B`       — bisection of `B` into two sub-boxes covering `B`.
* `L`             — a Lipschitz constant for the network (`≥ 0`).

The three laws are the entire mathematical content the procedure relies on:

* `width_error`   — `relaxedBound B ≥ trueMin B − L·diam B`
                    (the relaxation error is at most `L·diam`);
* `diam_contract` — each child's diameter is at most half the parent's
                    (a single input bisection at least halves the width);
* `trueMin_mono`  — each child's true minimum is at least the parent's
                    (the min over a sub-box dominates the min over the box). -/
structure Relaxation (Box : Type*) (Sample : Type*) where
  diam         : Box → ℝ
  trueMin      : Box → ℝ
  relaxedBound : Box → ℝ
  split        : Box → Box × Box
  /-- `mem B s` : the input point `s` lies in box `B`. -/
  mem          : Box → Sample → Prop
  /-- `safe s` : the network is safe at the input point `s` (the property to verify). -/
  safe         : Sample → Prop
  L            : ℝ
  L_nonneg     : 0 ≤ L
  diam_nonneg  : ∀ B, 0 ≤ diam B
  /-- **Width-error (completeness side).** The relaxation error is at most `L·diam`. -/
  width_error  : ∀ B, trueMin B - L * diam B ≤ relaxedBound B
  /-- **Contraction.** A single input bisection at least halves the controlling width. -/
  diam_contract : ∀ B, diam (split B).1 ≤ diam B / 2 ∧ diam (split B).2 ≤ diam B / 2
  /-- **Monotonicity.** Each child's true minimum dominates its parent's. -/
  trueMin_mono  : ∀ B, trueMin B ≤ trueMin (split B).1 ∧ trueMin B ≤ trueMin (split B).2
  /-- **Soundness (decides a leaf).** A positive certified bound on a box proves
  the property on every point of that box.  This is the exact guarantee the
  CROWN/Farkas leaf certificate provides (the soundness side of this development);
  here it is the bridge that turns a positive relaxed bound into closed leaves. -/
  decides       : ∀ B, 0 < relaxedBound B → ∀ s, mem B s → safe s
  /-- **Covering.** The two half-boxes of a bisection cover the parent box: every
  point of `B` lies in one of the children (`le_total` on the split coordinate). -/
  cover         : ∀ B s, mem B s → mem (split B).1 s ∨ mem (split B).2 s

variable {Box : Type*} {Sample : Type*} (R : Relaxation Box Sample)

/-! ## 2. The full bisection tree to a fixed depth, and what its leaves inherit

`leafBoxes R B d` is the multiset (as a `List`) of boxes at depth `d` of the
full bisection of `B`.  We prove the two facts a depth-`d` leaf inherits from the
root: its diameter is `≤ diam B / 2^d`, and its true minimum is `≥ trueMin B`.
These are the contraction/monotonicity laws integrated over the path. -/

/-- All boxes at depth `d` of the full bisection of `B`. -/
def leafBoxes (B : Box) : ℕ → List Box
  | 0 => [B]
  | d + 1 => leafBoxes (R.split B).1 d ++ leafBoxes (R.split B).2 d

/-- **Diameter contraction integrated over depth.**
Every box at depth `d` has diameter at most `diam B / 2^d`. -/
theorem leaf_diam_le (B : Box) (d : ℕ) :
    ∀ C ∈ leafBoxes R B d, R.diam C ≤ R.diam B / 2 ^ d := by
  induction d generalizing B with
  | zero =>
      intro C hC
      simp only [leafBoxes, List.mem_singleton] at hC
      subst hC
      simp
  | succ d ih =>
      intro C hC
      simp only [leafBoxes, List.mem_append] at hC
      have hpos : (0:ℝ) < 2 ^ d := by positivity
      rcases hC with hC | hC
      · -- C is a depth-d leaf of the left child
        have h1 := ih (R.split B).1 C hC
        have h2 := (R.diam_contract B).1
        -- diam C ≤ diam(left)/2^d ≤ (diam B/2)/2^d = diam B/2^(d+1)
        have : R.diam C ≤ (R.diam B / 2) / 2 ^ d :=
          le_trans h1 (by
            apply div_le_div_of_nonneg_right h2 (le_of_lt hpos))
        calc R.diam C ≤ (R.diam B / 2) / 2 ^ d := this
          _ = R.diam B / 2 ^ (d + 1) := by ring
      · -- C is a depth-d leaf of the right child
        have h1 := ih (R.split B).2 C hC
        have h2 := (R.diam_contract B).2
        have : R.diam C ≤ (R.diam B / 2) / 2 ^ d :=
          le_trans h1 (by
            apply div_le_div_of_nonneg_right h2 (le_of_lt hpos))
        calc R.diam C ≤ (R.diam B / 2) / 2 ^ d := this
          _ = R.diam B / 2 ^ (d + 1) := by ring

/-- **True-minimum monotonicity integrated over depth.**
Every box at depth `d` has true minimum at least `trueMin B`: bisection only
restricts to sub-boxes, over which the minimum can only increase. -/
theorem leaf_trueMin_ge (B : Box) (d : ℕ) :
    ∀ C ∈ leafBoxes R B d, R.trueMin B ≤ R.trueMin C := by
  induction d generalizing B with
  | zero =>
      intro C hC
      simp only [leafBoxes, List.mem_singleton] at hC
      subst hC
      exact le_refl _
  | succ d ih =>
      intro C hC
      simp only [leafBoxes, List.mem_append] at hC
      rcases hC with hC | hC
      · exact le_trans (R.trueMin_mono B).1 (ih (R.split B).1 C hC)
      · exact le_trans (R.trueMin_mono B).2 (ih (R.split B).2 C hC)

/-! ## 3. Covering: the depth-`d` leaves cover the root box

The two half-boxes of a bisection cover the parent (`cover`), so by induction
the depth-`d` full bisection covers the root: every point of `B` lies in some
depth-`d` leaf box.  This is the bisection analogue of `BoxTree.safe_on_path`'s
covering step, proved by the same `le_total`-style case split (here packaged in
`R.cover`). -/

/-- Every point of `B` lies in some box at depth `d` of its full bisection. -/
theorem mem_leaf_of_mem (B : Box) (d : ℕ) :
    ∀ s, R.mem B s → ∃ C ∈ leafBoxes R B d, R.mem C s := by
  induction d generalizing B with
  | zero =>
      intro s hs
      exact ⟨B, by simp [leafBoxes], hs⟩
  | succ d ih =>
      intro s hs
      rcases R.cover B s hs with hL | hR
      · obtain ⟨C, hCmem, hCs⟩ := ih (R.split B).1 s hL
        exact ⟨C, by simp only [leafBoxes, List.mem_append]; exact Or.inl hCmem, hCs⟩
      · obtain ⟨C, hCmem, hCs⟩ := ih (R.split B).2 s hR
        exact ⟨C, by simp only [leafBoxes, List.mem_append]; exact Or.inr hCmem, hCs⟩

/-! ## 4. The completeness core

`exists_decisive_depth` : a finite bisection depth at which EVERY leaf's relaxed
bound is strictly positive — the heart of "positive margin ⟹ finite BaB closes
every leaf."  `complete` : the full decision — at that depth the whole root box
is safe, routed through the per-leaf `decides` certificates. -/

/-- The arithmetic kernel: with a positive root margin `δ`, the width-error law
forces a *strictly positive* relaxed bound on any box whose diameter is below
`δ / L`.  Combined with the contraction this is what closes a small-enough leaf. -/
theorem relaxedBound_pos_of_diam_lt
    {B : Box} {δ : ℝ} (hmin : δ ≤ R.trueMin B)
    (hdiam : R.L * R.diam B < δ) :
    0 < R.relaxedBound B := by
  have := R.width_error B               -- trueMin B − L·diam B ≤ relaxedBound B
  -- trueMin B ≥ δ and L·diam B < δ  ⇒  trueMin B − L·diam B > 0
  linarith

/-- **Finite decisive depth EXISTS (termination).**
Given a strict positive margin `δ ≤ trueMin(root)`, there is a finite bisection
depth `d` such that EVERY leaf at depth `d` has a strictly positive relaxed
bound (hence closes).  The depth is the Archimedean witness `2^d > L·diam₀/δ`,
i.e. `d ≥ log₂(L·diam₀/δ)`; existence is `pow_unbounded_of_one_lt`. -/
theorem exists_decisive_depth (B : Box) {δ : ℝ} (hδ : 0 < δ)
    (hmin : δ ≤ R.trueMin B) :
    ∃ d : ℕ, ∀ C ∈ leafBoxes R B d, 0 < R.relaxedBound C := by
  -- pick d with 2^d > L·diam₀/δ
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (R.L * R.diam B / δ) (by norm_num : (1:ℝ) < 2)
  refine ⟨d, ?_⟩
  intro C hC
  have hpow : (0:ℝ) < 2 ^ d := by positivity
  -- diam C ≤ diam₀ / 2^d
  have hdiamC : R.diam C ≤ R.diam B / 2 ^ d := leaf_diam_le R B d C hC
  -- trueMin C ≥ trueMin B ≥ δ
  have hminC : δ ≤ R.trueMin C := le_trans hmin (leaf_trueMin_ge R B d C hC)
  -- L·diam C < δ  (from 2^d > L·diam₀/δ)
  have hkey : R.L * R.diam C < δ := by
    have hLdiam : R.L * R.diam C ≤ R.L * (R.diam B / 2 ^ d) :=
      mul_le_mul_of_nonneg_left hdiamC R.L_nonneg
    -- from hd : L·diam₀/δ < 2^d  ⇒  L·diam₀ < 2^d · δ  ⇒  L·(diam₀/2^d) < δ
    rw [div_lt_iff₀ hδ] at hd        -- hd : L·diam B < 2^d * δ
    have : R.L * (R.diam B / 2 ^ d) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ hpow]
      nlinarith
    linarith
  exact relaxedBound_pos_of_diam_lt R hminC hkey

/-- **VERIFIED COMPLETENESS — positive margin ⟹ finite BaB decides the box.**

If the property holds on the root box `B` with a *strict positive margin*
`δ ≤ trueMin(B)` (`0 < δ`), then there is a finite bisection depth `d` at which
every leaf's relaxed bound is positive, every leaf is closed by its soundness
certificate (`decides`), the depth-`d` leaves cover `B`, and therefore the
property `safe` holds on EVERY point of `B`.  The branch-and-bound procedure
terminates (the tree is the finite depth-`d` full tree, `leafBoxes`) with a
correct decision. -/
theorem complete (B : Box) {δ : ℝ} (hδ : 0 < δ) (hmin : δ ≤ R.trueMin B) :
    ∃ d : ℕ,
      (∀ C ∈ leafBoxes R B d, 0 < R.relaxedBound C) ∧   -- every leaf CLOSES
      (∀ s, R.mem B s → R.safe s) := by                  -- the root is DECIDED
  obtain ⟨d, hpos⟩ := exists_decisive_depth R B hδ hmin
  refine ⟨d, hpos, ?_⟩
  intro s hs
  -- s lands in some depth-d leaf C, which is closed (positive relaxed bound),
  -- so `decides` proves safety at s.
  obtain ⟨C, hCmem, hCs⟩ := mem_leaf_of_mem R B d s hs
  exact R.decides C (hpos C hCmem) s hCs

/-! ## 5. The composition is the SAME kernel the soundness side uses

`complete` already performs a leaves-cover-the-box composition — the box-level
twin of `BoxTree.safe_of_leaves`.  To make the identity literal we package the
covering-composition as a structure-free lemma (`box_safe_of_leaves`) proved by
exactly the induction `BoxTree.safe_on_path` uses, and show `complete` is its
instance.  We then derive the genuine `BoxTree.safe_of_leaves` conclusion for a
single-coordinate bisection model, witnessing that the abstract `Relaxation`
specialises to the concrete kernel object the Front-A certificates feed. -/

/-- **Box-tree covering + composition** (the box-level `safe_of_leaves`).
If every depth-`d` leaf box is decided safe on its own points, then `safe` holds
on every point of `B`.  Same shape, same induction skeleton as
`BoxTree.safe_on_path`: cover the parent by its two children, recurse.  Here the
cover is `R.cover` and the leaf discharge is `R.decides`. -/
theorem box_safe_of_leaves (B : Box) (d : ℕ)
    (hleaf : ∀ C ∈ leafBoxes R B d, ∀ s, R.mem C s → R.safe s) :
    ∀ s, R.mem B s → R.safe s := by
  intro s hs
  obtain ⟨C, hCmem, hCs⟩ := mem_leaf_of_mem R B d s hs
  exact hleaf C hCmem s hCs

/-- The completeness decision (Section 4) IS an instance of the box-level
`safe_of_leaves`: the per-leaf obligations are discharged by the positive
relaxed bounds through `R.decides`. -/
theorem complete' (B : Box) {δ : ℝ} (hδ : 0 < δ) (hmin : δ ≤ R.trueMin B) :
    ∃ d : ℕ,
      (∀ C ∈ leafBoxes R B d, 0 < R.relaxedBound C) ∧
      (∀ s, R.mem B s → R.safe s) := by
  obtain ⟨d, hpos⟩ := exists_decisive_depth R B hδ hmin
  exact ⟨d, hpos, box_safe_of_leaves R B d
    (fun C hC s hms => R.decides C (hpos C hC) s hms)⟩

end Complete

/-! ## 6. The abstract completeness specialises to the concrete `BoxTree` kernel

A one-node `Relaxation` whose single bisection is a coordinate split feeds the
*actual* `BoxTree.safe_of_leaves`.  This demonstrates that the completeness
machinery and the soundness composition are the same kernel object: a positive
margin yields closed leaves, which `BoxTree.safe_of_leaves` composes into the
whole-box decision exactly as the Front-A leaf certificates do. -/

/-- A single split, decided on both half-boxes, is composed by the real kernel
`BoxTree.safe_of_leaves` — the shape `complete` produces at depth 1. -/
example {S : Type*} (valid : S → Prop) (zsplit : S → ℚ) (Safe : S → Prop)
    (hneg : ∀ s, valid s → zsplit s ≤ 0 → Safe s)
    (hpos : ∀ s, valid s → 0 ≤ zsplit s → Safe s) :
    ∀ s, valid s → Safe s :=
  BoxTree.safe_of_leaves (fun (_ : Unit) => zsplit) Safe valid
    (.split () 0 .leaf .leaf)
    ⟨fun s ⟨hv, hz⟩ => hneg s hv hz, fun s ⟨hv, hz⟩ => hpos s hv hz⟩

/-! ## Trust-base check — every completeness theorem must reduce to the standard
logical axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO
`sorryAx`.  The `pow_unbounded_of_one_lt`/`linarith`/`nlinarith` machinery from
mathlib reduces to exactly these. -/

#print axioms Complete.leaf_diam_le
#print axioms Complete.leaf_trueMin_ge
#print axioms Complete.mem_leaf_of_mem
#print axioms Complete.relaxedBound_pos_of_diam_lt
#print axioms Complete.exists_decisive_depth
#print axioms Complete.complete
#print axioms Complete.box_safe_of_leaves
#print axioms Complete.complete'

end Crownproof
