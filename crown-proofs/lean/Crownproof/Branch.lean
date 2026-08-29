/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Branch-and-bound (β-CROWN) soundness as a certificate-carrying proof tree.

Hard verification instances are not closed by a single convex relaxation; the
verifier SPLITS an unstable ReLU on the sign of its pre-activation and bounds
each half-box (where that ReLU is now stable, so the relaxation is exact and
tighter).  This file proves the soundness of that mechanism: a verdict assembled
from per-branch bounds is itself a sound bound.  Each leaf is discharged by a
Farkas/CROWN certificate (`Crownproof.crown_bridge` / `farkas_premise_combination`);
this is the *composition rule* of the proof tree — the β-CROWN analogue of
`Or.elim` over the split.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.MinMax

namespace Crownproof

/--
**Single split soundness.**  Splitting on the sign of any quantity `zsplit` is a
sound case analysis: if the bound `b` holds on the `zsplit ≤ 0` branch and on the
`zsplit ≥ 0` branch, it holds everywhere.  (`le_total` — every point lands in one
branch.)
-/
theorem branch_split_sound {S : Type*}
    (valid : S → Prop) (zsplit out : S → ℚ) (b : ℚ)
    (hneg : ∀ s, valid s → zsplit s ≤ 0 → b ≤ out s)
    (hpos : ∀ s, valid s → 0 ≤ zsplit s → b ≤ out s) :
    ∀ s, valid s → b ≤ out s := by
  intro s hv
  rcases le_total (zsplit s) 0 with h | h
  · exact hneg s hv h
  · exact hpos s hv h

/--
**Split with per-branch bounds (the β-CROWN leaf-combination rule).**  When the
two branches certify *different* bounds `bneg`, `bpos`, the verdict for the whole
box is their minimum.  This is exactly how branch-and-bound assembles a global
bound from a frontier of sub-problems.
-/
theorem branch_split_min {S : Type*}
    (valid : S → Prop) (zsplit out : S → ℚ) (bneg bpos : ℚ)
    (hneg : ∀ s, valid s → zsplit s ≤ 0 → bneg ≤ out s)
    (hpos : ∀ s, valid s → 0 ≤ zsplit s → bpos ≤ out s) :
    ∀ s, valid s → min bneg bpos ≤ out s := by
  intro s hv
  rcases le_total (zsplit s) 0 with h | h
  · exact le_trans (min_le_left bneg bpos) (hneg s hv h)
  · exact le_trans (min_le_right bneg bpos) (hpos s hv h)

/--
**Depth-2 proof tree.**  Splitting on `z1`, then splitting the `z1 ≥ 0` branch
again on `z2`, gives three leaves; the global bound is the min of the three leaf
bounds.  Demonstrates that the combination rule composes into a tree — the
general β-CROWN search tree is this rule applied recursively, and its soundness
is `branch_split_min` at every internal node.
-/
theorem branch_tree_depth2 {S : Type*}
    (valid : S → Prop) (z1 z2 out : S → ℚ) (b00 b10 b11 : ℚ)
    -- leaf z1 ≤ 0
    (h0 : ∀ s, valid s → z1 s ≤ 0 → b00 ≤ out s)
    -- leaf z1 ≥ 0, z2 ≤ 0
    (h10 : ∀ s, valid s → 0 ≤ z1 s → z2 s ≤ 0 → b10 ≤ out s)
    -- leaf z1 ≥ 0, z2 ≥ 0
    (h11 : ∀ s, valid s → 0 ≤ z1 s → 0 ≤ z2 s → b11 ≤ out s) :
    ∀ s, valid s → min b00 (min b10 b11) ≤ out s := by
  -- Split on z1 with the right branch handled by a nested split on z2.
  apply branch_split_min valid z1 out b00 (min b10 b11)
  · intro s hv hz1
    exact h0 s hv hz1
  · -- right branch (z1 ≥ 0): split on z2, bound = min b10 b11
    intro s hv hz1
    rcases le_total (z2 s) 0 with hz2 | hz2
    · exact le_trans (min_le_left b10 b11) (h10 s hv hz1 hz2)
    · exact le_trans (min_le_right b10 b11) (h11 s hv hz1 hz2)

/-! Trust-base check. -/
#print axioms branch_split_sound
#print axioms branch_split_min
#print axioms branch_tree_depth2

end Crownproof
