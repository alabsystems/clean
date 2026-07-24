/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto2_finite_monotone_iterate_reaches_fixedPoint`
(finite order theory — a CONSTRUCTIVE Knaster–Tarski via iteration).

────────────────────────────────────────────────────────────────────────────
WHAT THIS IS
────────────────────────────────────────────────────────────────────────────
Mathlib's Knaster–Tarski (`OrderHom.lfp`, `Mathlib/Order/FixedPoints.lean`)
proves a least fixed point EXISTS in a complete lattice, defined NON-
constructively as `sInf { a | f a ≤ a }`.  It does NOT exhibit the fixed point
as an explicit iterate, and it is stated for complete lattices, not finite
orders.  Separately, `Monotone.monotone_iterate_of_le_map`
(`Mathlib/Order/Iterate.lean`) shows the iterates `f^[n] x` of a monotone `f`
form a monotone sequence when `x ≤ f x`, but says NOTHING about whether they
reach a fixed point.

This file states and proves the combination that Mathlib does not state: in a
FINITE partial order, the iterates of a monotone self-map `f`, started from any
PRE-FIXED point `x` (i.e. `x ≤ f x`), reach an ACTUAL fixed point of `f` after
finitely many steps, and that fixed point lies above `x`.  This is a
constructive, iteration-based Knaster–Tarski for finite orders: the fixed point
is produced as a concrete iterate `f^[n] x`, not as an abstract infimum.

────────────────────────────────────────────────────────────────────────────
PROOF SHAPE (foundational; no domain axioms)
────────────────────────────────────────────────────────────────────────────
1.  `Monotone.monotone_iterate_of_le_map` : `n ↦ f^[n] x` is monotone.
2.  A finite `PartialOrder` is `WellFoundedGT` (no infinite strictly-increasing
    chains), so `WellFoundedGT.monotone_chain_condition` gives an index `n`
    past which the monotone sequence is constant; in particular
    `f^[n] x = f^[n+1] x`.
3.  `Function.iterate_succ_apply'` rewrites `f^[n+1] x = f (f^[n] x)`, so
    `f (f^[n] x) = f^[n] x`: `f^[n] x` is a fixed point.
4.  `x = f^[0] x ≤ f^[n] x` by monotonicity of the sequence (`Nat.zero_le n`).

────────────────────────────────────────────────────────────────────────────
NOVELTY
────────────────────────────────────────────────────────────────────────────
N1 first-formalization: Mathlib has lfp-exists (non-constructive, complete
lattice) and monotone-iterate-is-monotone, but not "finite + monotone +
pre-fixed point ⟹ an iterate is a fixed point above the start."  No equivalent
statement was found by grepping the mathlib source (see the agent report).
This is folklore (finite Kleene/Tarski iteration) but is NOT a stated Mathlib
lemma.
-/
-- Minimal imports (was bare `import Mathlib`, which dragged the full-Mathlib olean
-- closure into graduation, >1h to load): only the modules this proof actually needs —
-- monotone-iterate (Order.Iterate), the monotone chain condition + Finite⟹WellFoundedGT
-- (Order.OrderIsoNat), iterate_succ_apply' (Logic.Function.Iterate), OrderHom (Order.Hom.Basic).
import Mathlib.Order.Iterate
import Mathlib.Order.OrderIsoNat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Hom.Basic

namespace Crownproof.InventionWave5

open Function

/-- **Constructive finite Knaster–Tarski (iteration form).**
In a finite partial order, if `f` is monotone and `x` is a pre-fixed point
(`x ≤ f x`), then iterating `f` from `x` reaches an honest fixed point of `f`
after finitely many steps, and that fixed point lies above `x`.

The fixed point is produced as an explicit iterate `f^[n] x` — unlike Mathlib's
`OrderHom.lfp`, which is the non-constructive `sInf {a | f a ≤ a}` and requires
a complete lattice. -/
theorem auto2_finite_monotone_iterate_reaches_fixedPoint
    {α : Type*} [PartialOrder α] [Finite α]
    {f : α → α} (hf : Monotone f) {x : α} (hx : x ≤ f x) :
    ∃ n : ℕ, f (f^[n] x) = f^[n] x ∧ x ≤ f^[n] x := by
  -- The iterate sequence is monotone, package it as a bundled `ℕ →o α`.
  have hmono : Monotone fun n : ℕ => f^[n] x := hf.monotone_iterate_of_le_map hx
  let a : ℕ →o α := ⟨fun n => f^[n] x, hmono⟩
  -- A finite partial order satisfies the monotone chain condition.
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨n, ?_, ?_⟩
  · -- The sequence is constant from `n` on; in particular at `n+1`.
    have hconst : a n = a (n + 1) := hn (n + 1) (Nat.le_succ n)
    -- `a (n+1) = f (f^[n] x)`.
    have hsucc : a (n + 1) = f (f^[n] x) := iterate_succ_apply' f n x
    -- Combine: `f (f^[n] x) = f^[n] x`.
    simpa [a, hsucc] using hconst.symm
  · -- `x = f^[0] x ≤ f^[n] x` by monotonicity of the sequence.
    have : a 0 ≤ a n := hmono (Nat.zero_le n)
    simpa [a] using this

end Crownproof.InventionWave5
