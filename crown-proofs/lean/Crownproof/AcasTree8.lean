/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

The Front-B composition instantiated on the ACTUAL 8-leaf bisection tree produced
for a real ACAS-Xu prop_1 / net_1_1 sub-box.

`BranchTree.lean` proves the generic whole-tree composition
`BoxTree.safe_of_leaves` (safe-on-every-leaf ⇒ safe-on-root) for an arbitrary
input-bisection tree.  Here we pin that theorem to the *exact* tree shape the
driver emitted — a depth-3 balanced bisection of coordinates X₀, X₃, X₄ at the
rational midpoints 16/25, 19/40, −19/40 — and to the ACAS semantics:

  * `S = Fin 5 → ℚ`            a point of the (rational) input box;
  * `coord i s = s i`          read input coordinate i;
  * `Safe s`                   the safety predicate (unsafe atom Y₀ ≥ c is false);
                               each leaf's Clean-PASSED Farkas cert establishes
                               `Safe` on that leaf's box, i.e. the leaf obligation;
  * `inRegion s`               membership in the root sub-box
                               [0.636,0.644]×[-0.004,0.004]²×[0.471,0.479]×[-0.479,-0.471].

`acas_tree8_decision` states: given the 8 per-leaf safety facts (exactly the
Clean-PASSED leaf certificates, one per closed leaf box), `Safe` holds on the
whole root sub-box.  It is proved purely by `BoxTree.safe_of_leaves`, so the
covering/composition is machine-checked for the concrete tree.  `#print axioms`
shows only Lean/Mathlib's standard trust base.
-/
import Crownproof.BranchTree

namespace Crownproof

open BoxTree

/-- Input point: five rational coordinates. -/
abbrev Pt := Fin 5 → ℚ

/-- Coordinate readout. -/
def acoord (i : Fin 5) (s : Pt) : ℚ := s i

/-- The root sub-box membership predicate (the real ACAS prop_1 sub-box). -/
def rootBox (s : Pt) : Prop :=
  (633/1000 + 3/1000 ≤ s 0 ∧ s 0 ≤ 644/1000) ∧   -- X₀ ∈ [0.636, 0.644]
  (-(4/1000) ≤ s 1 ∧ s 1 ≤ 4/1000) ∧             -- X₁ ∈ [-0.004, 0.004]
  (-(4/1000) ≤ s 2 ∧ s 2 ≤ 4/1000) ∧             -- X₂ ∈ [-0.004, 0.004]
  (471/1000 ≤ s 3 ∧ s 3 ≤ 479/1000) ∧            -- X₃ ∈ [0.471, 0.479]
  (-(479/1000) ≤ s 4 ∧ s 4 ≤ -(471/1000))        -- X₄ ∈ [-0.479, -0.471]

/-- The exact 8-leaf bisection tree emitted by the driver: split X₀ at 16/25,
then X₃ at 19/40, then X₄ at −19/40 (a depth-3 balanced tree). -/
def acasTree8 : BoxTree (Fin 5) :=
  .split 0 (16/25)
    (.split 3 (19/40)
      (.split 4 (-19/40) .leaf .leaf)
      (.split 4 (-19/40) .leaf .leaf))
    (.split 3 (19/40)
      (.split 4 (-19/40) .leaf .leaf)
      (.split 4 (-19/40) .leaf .leaf))

/--
**Whole-(sub)box decision for the real ACAS 8-leaf tree.**
The eight hypotheses are precisely the per-leaf safety facts established by the
eight Clean-PASSED Farkas certificates (each leaf box stated by its accumulated
half-box cuts).  The conclusion — `Safe` on the entire root sub-box — follows
from the generic, machine-checked composition `BoxTree.safe_of_leaves`.

We phrase it via `Leaves` so the leaf obligations are read off the tree exactly
as the driver/Clean produce them; the proof is one `exact safe_of_leaves …`.
-/
theorem acas_tree8_decision (Safe : Pt → Prop)
    (hleaves : Leaves acoord Safe acasTree8 rootBox) :
    ∀ s, rootBox s → Safe s :=
  safe_of_leaves acoord Safe rootBox acasTree8 hleaves

/-- Equivalent fully-unfolded statement of the eight leaf obligations, to make the
per-leaf hypotheses explicit (each conjunct is one leaf's "Safe on this box").
`bif`-free; the half-box cuts are the literal `≤`/`≥` against the midpoints. -/
theorem acas_tree8_decision_explicit (Safe : Pt → Prop)
    -- leaf 0: x0≤16/25, x3≤19/40, x4≤-19/40
    (h0 : ∀ s, ((((rootBox s ∧ acoord 0 s ≤ 16/25) ∧ acoord 3 s ≤ 19/40)
                  ∧ acoord 4 s ≤ -19/40)) → Safe s)
    -- leaf 1: x0≤16/25, x3≤19/40, x4≥-19/40
    (h1 : ∀ s, ((((rootBox s ∧ acoord 0 s ≤ 16/25) ∧ acoord 3 s ≤ 19/40)
                  ∧ (-19/40 : ℚ) ≤ acoord 4 s)) → Safe s)
    -- leaf 2: x0≤16/25, x3≥19/40, x4≤-19/40
    (h2 : ∀ s, ((((rootBox s ∧ acoord 0 s ≤ 16/25) ∧ (19/40 : ℚ) ≤ acoord 3 s)
                  ∧ acoord 4 s ≤ -19/40)) → Safe s)
    -- leaf 3: x0≤16/25, x3≥19/40, x4≥-19/40
    (h3 : ∀ s, ((((rootBox s ∧ acoord 0 s ≤ 16/25) ∧ (19/40 : ℚ) ≤ acoord 3 s)
                  ∧ (-19/40 : ℚ) ≤ acoord 4 s)) → Safe s)
    -- leaf 4: x0≥16/25, x3≤19/40, x4≤-19/40
    (h4 : ∀ s, ((((rootBox s ∧ (16/25 : ℚ) ≤ acoord 0 s) ∧ acoord 3 s ≤ 19/40)
                  ∧ acoord 4 s ≤ -19/40)) → Safe s)
    -- leaf 5: x0≥16/25, x3≤19/40, x4≥-19/40
    (h5 : ∀ s, ((((rootBox s ∧ (16/25 : ℚ) ≤ acoord 0 s) ∧ acoord 3 s ≤ 19/40)
                  ∧ (-19/40 : ℚ) ≤ acoord 4 s)) → Safe s)
    -- leaf 6: x0≥16/25, x3≥19/40, x4≤-19/40
    (h6 : ∀ s, ((((rootBox s ∧ (16/25 : ℚ) ≤ acoord 0 s) ∧ (19/40 : ℚ) ≤ acoord 3 s)
                  ∧ acoord 4 s ≤ -19/40)) → Safe s)
    -- leaf 7: x0≥16/25, x3≥19/40, x4≥-19/40
    (h7 : ∀ s, ((((rootBox s ∧ (16/25 : ℚ) ≤ acoord 0 s) ∧ (19/40 : ℚ) ≤ acoord 3 s)
                  ∧ (-19/40 : ℚ) ≤ acoord 4 s)) → Safe s) :
    ∀ s, rootBox s → Safe s := by
  refine acas_tree8_decision Safe ?_
  -- assemble the eight obligations into the tree's `Leaves` structure
  exact ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨h4, h5⟩, ⟨h6, h7⟩⟩⟩

#print axioms acas_tree8_decision
#print axioms acas_tree8_decision_explicit

end Crownproof
