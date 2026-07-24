-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: RECURSION THROUGH A PROJECTION (Track H, task 1).
--
-- A recursive method may match on a *projection* of its decreasing binder
-- rather than on the binder itself, rebuilding a wrapper around the smaller
-- sub-component for the recursive call:
--
--   def Box.len (b : Box) : Nat :=
--     match b.data with
--     | Lst.nil      => 0
--     | Lst.cons _ t => Nat.succ (Box.len { data := t })
--
-- This is NOT structural recursion on `Box` (a non-recursive single-field
-- struct): `Box.rec` performs only one level of case analysis, and the
-- recursive call passes a freshly-built `{ data := t }`, not a sub-term of `b`.
-- The recursion is genuinely structural on the PROJECTED FIELD `b.data : Lst`.
-- Before this change the def failed to elaborate — no `RecursiveDefContext` was
-- installed and the self-name `Box.len` was left unresolved (`UnknownIdent`).
--
-- Clean now desugars this shape into an auxiliary equation-form def recursing
-- structurally on the projected field's inductive, plus a thin wrapper:
--
--   def Box.len.go : Lst -> Nat
--     | Lst.nil      => 0
--     | Lst.cons _ t => Nat.succ (Box.len.go t)
--   def Box.len (b : Box) : Nat := Box.len.go b.data
--
-- The auxiliary def routes through the already-proven equation-form `T.rec`
-- lowering — genuine structural recursion, no faked termination, zero new
-- kernel reducers. The `rfl` theorems force the kernel to fully reduce the
-- lowered `Lst.rec` applications, confirming the lowered terms compute.

inductive Lst where
  | nil : Lst
  | cons : Nat -> Lst -> Lst

structure Box where
  data : Lst

def Box.len (b : Box) : Nat :=
  match b.data with
  | Lst.nil => 0
  | Lst.cons _ t => Nat.succ (Box.len { data := t })

-- Computational checks: each `rfl` requires the kernel to reduce the recursive
-- `Lst.rec` term wrapped by the projection.
theorem boxlen_nil : Box.len { data := Lst.nil } = 0 := rfl
theorem boxlen_one : Box.len { data := Lst.cons 7 Lst.nil } = 1 := rfl
theorem boxlen_two : Box.len { data := Lst.cons 7 (Lst.cons 9 Lst.nil) } = 2 := rfl
theorem boxlen_three :
    Box.len { data := Lst.cons 7 (Lst.cons 9 (Lst.cons 5 Lst.nil)) } = 3 := rfl
