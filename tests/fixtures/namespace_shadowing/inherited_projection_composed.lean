-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- The composed inherited-field projection is DEFINITIONALLY EQUAL to the
-- constant Clean materializes for it, and the equality is discharged BY THE
-- KERNEL (`rfl`), not asserted by a test.
--
-- Lean 4 declares no constant for an inherited field; `x.widget` on a `MyDer`
-- is composed at the use site as `MyBase.widget (MyDer.toMyBase x)`
-- (`mkBaseProjections`, `src/Lean/Elab/App.lean`). Clean ADDITIONALLY registers
-- `MyDer.widget` as a real constant. If the two are definitionally equal, then
-- dropping the constant and composing on the fly cannot change any term's
-- meaning — which is the precondition for closing the divergence at all.
-- See `designs/2026-08-24-inherited-projection-parity.md`.
--
-- HOW THE TWO SIDES ARE FORCED APART.
--   `viaDot   x := x.widget`          — `widget` is NOT an own field of `MyDer`,
--                                       so `elab_proj` falls to `elab_dot_notation`,
--                                       which resolves the CONSTANT `MyDer.widget`.
--   `viaChain x := x.toMyBase.widget` — `toMyBase` IS an own field of `MyDer` and
--                                       `widget` IS an own field of `MyBase`, so
--                                       its body applies MyBase.widget to the
--                                       result of MyDer.toMyBase on x.
-- The companion Rust test checks the generated constant and the ordered
-- direct-field accessors down to the original record argument.

universe u

structure MyBase (a : Type u) where
  widget : a

structure MyDer (a : Type u) extends MyBase a where
  tag : Nat

structure MyTop (a : Type u) extends MyDer a where
  extra : Nat

-- One level of `extends`.
def viaDot (x : MyDer Nat) : Nat := x.widget

def viaChain (x : MyDer Nat) : Nat := x.toMyBase.widget

theorem composedEqGenerated (x : MyDer Nat) : viaDot x = viaChain x := rfl

-- Two levels: the grandparent's field, where the composer must recurse. Clean
-- re-exposes grandparent fields transitively, so `MyTop.widget` is generated
-- too and this is again constant-vs-chain.
def viaDotDeep (y : MyTop Nat) : Nat := y.widget

def viaChainDeep (y : MyTop Nat) : Nat := y.toMyDer.toMyBase.widget

theorem composedEqGeneratedDeep (y : MyTop Nat) : viaDotDeep y = viaChainDeep y := rfl

-- The inherited field still reads the value that was put there, through both
-- routes: a VALUE-distinguishing check, so neither side can be vacuously equal
-- by both being stuck.
def sample : MyTop Nat := { widget := 7, tag := 1, extra := 2 }

theorem sampleDot : viaDotDeep sample = 7 := rfl

theorem sampleChain : viaChainDeep sample = 7 := rfl
