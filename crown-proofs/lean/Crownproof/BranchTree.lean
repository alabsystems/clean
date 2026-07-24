/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WHOLE-TREE branch-and-bound composition as ONE kernel-checkable object.

`Branch.lean` proves the soundness of a *single* split and a fixed depth-2 tree.
This file lifts that to an **arbitrary input-bisection tree** of any shape, the
object a real β-CROWN / input-BaB run produces:

  * Each internal node bisects one input coordinate `x` at a rational midpoint `m`,
    splitting its region into the two CLOSED half-boxes `{x ≤ m}` and `{x ≥ m}`.
    These two half-boxes COVER the parent (every point satisfies `x ≤ m ∨ x ≥ m`,
    by `le_total`), so the leaves of the whole tree cover the root region.

  * Each LEAF carries a safety fact discharged by an exact-CROWN / Farkas
    certificate (`clean-extcert-verify` PASSED): the unsafe region is empty on
    that leaf box, i.e. the safety predicate `Safe` holds on every point of the
    leaf's region.

The theorem `BoxTree.safe_of_leaves` then composes the per-leaf safety facts
into whole-box safety:  Safe-on-every-leaf  ⟹  Safe-on-the-root-region.
This is the formal backbone that turns the Front-A leaf certificates into a
single machine-checked whole-box DECISION.  It specialises back to
`branch_split_sound` for a one-node tree and reproduces `branch_tree_depth2`'s
shape as a particular `BoxTree`.

We work over an abstract sample space `S` (a point of the input box) with:
  * `inRegion : S → Prop`  — the *root* region (the input box membership test);
  * coordinate readouts `coord : Coord → S → ℚ` for the splittable inputs;
  * a safety predicate `Safe : S → Prop` (the negation of the unsafe atom).
A `BoxTree` refines the root region by accumulated path constraints; soundness
needs nothing about the geometry beyond `le_total` on ℚ, so it holds for the
real ACAS network's box exactly as for any toy instance.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.MinMax

namespace Crownproof

/-! ## The bisection tree -/

/-- An input-bisection proof tree.  `Coord` indexes the splittable input
coordinates; `coord c s` reads coordinate `c` of the sample `s`.

* `leaf` — a frontier box; the proof obligation is that `Safe` holds on every
  sample reaching this leaf (this is what an exact-CROWN / Farkas leaf cert
  establishes for the real network on that sub-box).
* `split c m lo hi` — bisect coordinate `c` at rational midpoint `m`; `lo`
  handles the `coord c s ≤ m` half-box, `hi` the `coord c s ≥ m` half-box. -/
inductive BoxTree (Coord : Type*) where
  | leaf : BoxTree Coord
  | split (c : Coord) (m : ℚ) (lo hi : BoxTree Coord) : BoxTree Coord
deriving Inhabited

namespace BoxTree

variable {S : Type*} {Coord : Type*}
variable (coord : Coord → S → ℚ) (Safe : S → Prop)

/-- The proof obligations a tree imposes, relative to a *path predicate* `path`
that accumulates the half-box constraints from the root to the current node.

* a `leaf` obliges: every sample on this path is `Safe`;
* a `split` obliges its two children under the path extended by `coord c · ≤ m`
  (resp. `≥ m`).

`Leaves` is the conjunction of all leaf obligations — exactly the set of
per-leaf certificates Front A must supply. -/
def Leaves : BoxTree Coord → ((S → Prop) → Prop)
  | leaf, path => ∀ s, path s → Safe s
  | split c m lo hi, path =>
      Leaves lo (fun s => path s ∧ coord c s ≤ m) ∧
      Leaves hi (fun s => path s ∧ m ≤ coord c s)

/--
**Whole-tree covering + composition (core soundness lemma).**
If every leaf obligation holds (relative to the path), then `Safe` holds on
every sample reaching this subtree.  The induction is over the tree; at each
`split` the two half-boxes cover the parent by `le_total (coord c s) m`, which
is exactly the "leaves cover the box" covering certificate, discharged
constructively.
-/
theorem safe_on_path :
    ∀ (t : BoxTree Coord) (path : S → Prop),
      Leaves coord Safe t path → ∀ s, path s → Safe s := by
  intro t
  induction t with
  | leaf =>
      intro path hleaf s hs
      exact hleaf s hs
  | split c m lo hi ihlo ihhi =>
      intro path hsplit s hs
      obtain ⟨hlo, hhi⟩ := hsplit
      -- Cover the parent region by the two closed half-boxes at `m`.
      rcases le_total (coord c s) m with hle | hge
      · exact ihlo _ hlo s ⟨hs, hle⟩
      · exact ihhi _ hhi s ⟨hs, hge⟩

/--
**Whole-box decision from leaf certificates.**
Instantiate the path at the root region `inRegion`.  If the tree's leaf
obligations all hold (the Front-A leaf certs) then `Safe` holds on the whole
root box.  This is the single kernel-checked statement
"safe on every leaf ⟹ safe on the box" for the *actual* tree shape produced by
the bisection.
-/
theorem safe_of_leaves (inRegion : S → Prop) (t : BoxTree Coord)
    (hleaves : Leaves coord Safe t inRegion) :
    ∀ s, inRegion s → Safe s :=
  safe_on_path coord Safe t inRegion hleaves

end BoxTree

/-! ## Sanity: the new tree object subsumes `Branch.lean`. -/

/-- A one-node tree reproduces `branch_split_sound`'s single split: the whole
box is `inRegion`, and the two half-boxes `z ≤ 0`, `z ≥ 0` are the leaves. -/
example {S : Type*} (valid : S → Prop) (zsplit : S → ℚ) (Safe : S → Prop)
    (hneg : ∀ s, valid s → zsplit s ≤ 0 → Safe s)
    (hpos : ∀ s, valid s → 0 ≤ zsplit s → Safe s) :
    ∀ s, valid s → Safe s := by
  -- one split at midpoint 0 on the single coordinate, both children leaves
  refine BoxTree.safe_of_leaves (fun (_ : Unit) => zsplit) Safe valid
      (.split () 0 .leaf .leaf) ?_
  constructor
  · intro s ⟨hv, hz⟩; exact hneg s hv hz
  · intro s ⟨hv, hz⟩; exact hpos s hv hz

/-- A depth-2 tree matching `branch_tree_depth2`'s shape (split on `z1`, then
split the `z1 ≥ 0` half on `z2`), with safety facts at the three leaves. -/
example {S : Type*} (valid : S → Prop) (z1 z2 : S → ℚ) (Safe : S → Prop)
    (h0  : ∀ s, valid s → z1 s ≤ 0 → Safe s)
    (h10 : ∀ s, valid s → 0 ≤ z1 s → z2 s ≤ 0 → Safe s)
    (h11 : ∀ s, valid s → 0 ≤ z1 s → 0 ≤ z2 s → Safe s) :
    ∀ s, valid s → Safe s := by
  -- Coord = Bool: false ↦ z1, true ↦ z2.
  refine BoxTree.safe_of_leaves
      (fun b : Bool => bif b then z2 else z1) Safe valid
      (.split false 0 .leaf (.split true 0 .leaf .leaf)) ?_
  refine ⟨?_, ?_, ?_⟩
  · intro s ⟨hv, hz1⟩; exact h0 s hv hz1
  · intro s ⟨⟨hv, hz1⟩, hz2⟩; exact h10 s hv hz1 hz2
  · intro s ⟨⟨hv, hz1⟩, hz2⟩; exact h11 s hv hz1 hz2

/-! ## Trust-base check (must be axiom-free up to Lean/Mathlib's standard core). -/

#print axioms BoxTree.safe_on_path
#print axioms BoxTree.safe_of_leaves

end Crownproof
