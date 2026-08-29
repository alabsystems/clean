/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

WHOLE-BOX composition for ACAS-Xu prop_1 / net_1_1.

This file pins the generic, machine-checked whole-tree composition
`Crownproof.BoxTree.safe_of_leaves` (BranchTree.lean) to the EXACT input-bisection
tree the float-fast/exact-slow driver emitted for the WHOLE prop_1 box — a tree of
47 leaves over the 5 input coordinates, every leaf closed by an exact bignum
CROWN Farkas refutation that the bignum Clean kernel PASSED.

  * `S = Fin 5 → ℚ`        a point of the (rational) prop_1 input box;
  * `coord i s = s i`      read input coordinate i;
  * `Safe s`               the safety predicate (unsafe atom Y₀ ≥ c is false);
  * `wholeBox s`           membership in the WHOLE prop_1 box
                           X₀∈[0.6,0.679857769], X₁,X₂∈[-0.5,0.5],
                           X₃∈[0.45,0.5], X₄∈[-0.5,-0.45].

`acas_wholebox_decision`: given the per-leaf safety facts (the Clean-PASSED leaf
certs, one per closed leaf box), `Safe` holds on the WHOLE prop_1 box. Proved by
`BoxTree.safe_of_leaves`; covering is by `le_total` at each split (machine-checked).
-/
import Crownproof.BranchTree

namespace Crownproof

open BoxTree

/-- Input point: five rational coordinates. -/
abbrev PtWB := Fin 5 → ℚ

/-- Coordinate readout. -/
def wbcoord (i : Fin 5) (s : PtWB) : ℚ := s i

/-- The WHOLE prop_1 input box. -/
def wholeBox (s : PtWB) : Prop :=
  ((3/5) ≤ s 0 ∧ s 0 ≤ (679857769/1000000000)) ∧
  ((-1/2) ≤ s 1 ∧ s 1 ≤ (1/2)) ∧
  ((-1/2) ≤ s 2 ∧ s 2 ≤ (1/2)) ∧
  ((9/20) ≤ s 3 ∧ s 3 ≤ (1/2)) ∧
  ((-1/2) ≤ s 4 ∧ s 4 ≤ (-9/20))

/-- The exact 47-leaf bisection tree emitted by the float-fast/exact-slow
driver for the whole prop_1 box (each `split c m` bisects coordinate `c` at the
exact rational midpoint `m`). -/
def acasWholeTree : BoxTree (Fin 5) :=
  (.split 1 (0) (.split 2 (0) (.split 1 (-1/4) .leaf (.split 2 (-1/4) (.split 1 (-1/8) .leaf .leaf) (.split 1 (-1/8) .leaf .leaf))) (.split 1 (-1/4) (.split 2 (1/4) (.split 1 (-3/8) (.split 2 (1/8) .leaf .leaf) (.split 2 (1/8) (.split 1 (-5/16) (.split 2 (1/16) .leaf .leaf) (.split 2 (1/16) (.split 0 (1279857769/2000000000) (.split 1 (-9/32) .leaf (.split 2 (1/32) .leaf .leaf)) (.split 1 (-9/32) .leaf (.split 2 (1/32) .leaf .leaf))) .leaf)) .leaf)) .leaf) (.split 2 (1/4) (.split 1 (-1/8) .leaf (.split 2 (1/8) .leaf .leaf)) (.split 1 (-1/8) .leaf (.split 2 (3/8) (.split 1 (-1/16) .leaf (.split 2 (5/16) (.split 0 (1279857769/2000000000) (.split 1 (-1/32) .leaf .leaf) (.split 1 (-1/32) .leaf .leaf)) (.split 0 (1279857769/2000000000) (.split 1 (-1/32) .leaf .leaf) (.split 1 (-1/32) .leaf .leaf)))) (.split 1 (-1/16) .leaf .leaf)))))) (.split 2 (0) (.split 1 (1/4) (.split 2 (-1/4) (.split 1 (1/8) (.split 2 (-3/8) .leaf .leaf) .leaf) (.split 1 (1/8) (.split 2 (-1/8) .leaf .leaf) .leaf)) (.split 2 (-1/4) .leaf (.split 1 (3/8) .leaf .leaf))) (.split 1 (1/4) (.split 2 (1/4) (.split 1 (1/8) .leaf .leaf) (.split 1 (1/8) .leaf .leaf)) .leaf)))

/--
**Whole-box decision for the real ACAS prop_1 / net_1_1 tree.**
Given the per-leaf safety facts (`Leaves`) — exactly the 47 Clean-PASSED
Farkas certificates, one per closed leaf box stated by its accumulated half-box
cuts — `Safe` holds on the ENTIRE prop_1 box. Proved by the generic, machine-checked
composition `BoxTree.safe_of_leaves` (covering by `le_total` at each split).
-/
theorem acas_wholebox_decision (Safe : PtWB → Prop)
    (hleaves : Leaves wbcoord Safe acasWholeTree wholeBox) :
    ∀ s, wholeBox s → Safe s :=
  safe_of_leaves wbcoord Safe wholeBox acasWholeTree hleaves

#print axioms acas_wholebox_decision

end Crownproof
