-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- NEGATIVE CONTROL for the C6 fix in `elab_ident`.
--
-- The fix passes over a derived inherited-field projection during the
-- current-namespace-outward walk so it cannot shadow a root/exported name.
-- It must NOT make the projection unreachable: when the bare name has no
-- other binding at all, resolution still lands on it (Lean would report
-- `unknown identifier` here instead — accepting more is safe, the kernel
-- re-checks every term), and the fully qualified name is unaffected.
--
-- `widget` is inherited from `MyBase` and exists nowhere else, so both
-- declarations resolved before the fix and must keep resolving after it.

universe u

structure MyBase (α : Type u) where
  widget : α

structure MyDer (α : Type u) extends MyBase α where
  tag : Nat

namespace MyDer

def viaBare (x : MyDer Nat) : Nat := widget x

def viaQualified (x : MyDer Nat) : Nat := MyDer.widget x

end MyDer
