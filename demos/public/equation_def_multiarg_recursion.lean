-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: MULTI-ARGUMENT equation-style RECURSIVE `def`s lowered to the
-- inductive's `.rec` eliminator (Task 3, slice 2 — follows the single-argument
-- slice 1 in equation_def_structural_recursion.lean).
--
-- A multi-argument equation def such as
--   `def append : Lst → Lst → Lst | nil, ys => ys | cons h t, ys => ... append t ys`
-- is desugared by the parser into a value
--   `PatternMatchLambda([_x], match _x with | Prod.mk p q => body | ...)`
-- with an EMPTY declaration-binder list (the `Lst → Lst → Lst` lives in the
-- type) and arm patterns that are right-nested `Prod.mk` tuples over the
-- per-argument patterns. Slice 1 explicitly DECLINED this `Prod.mk` shape, so a
-- recursive multi-arg def failed to elaborate: no `RecursiveDefContext` was
-- installed and the self-name was left unresolved (`UnknownIdent`).
--
-- Clean now lifts the synthetic `_x` binder into N named declaration binders
-- (peeling N domains off the arrow/Pi type) and rewrites the tuple match into a
-- single-scrutinee match on the *decreasing* position, so the existing,
-- already-proven single-argument structural recursion lowers through the
-- inductive's `.rec` — with the trailing pass-through arguments folded into the
-- motive via the established extra-param machinery. Genuine structural
-- recursion, no faked termination, zero new kernel reducers. The `rfl`
-- theorems force the kernel to fully reduce the lowered `.rec` applications,
-- confirming the lowered terms compute the intended values.

inductive Lst where
  | nil : Lst
  | cons : Nat → Lst → Lst

-- Multi-arg recursion on the FIRST argument; `ys` is a pass-through folded into
-- the motive. Lowers via `Lst.rec`.
def Lst.append : Lst → Lst → Lst
  | Lst.nil, ys => ys
  | Lst.cons h t, ys => Lst.cons h (Lst.append t ys)

-- Multi-arg recursion on `Nat`'s first argument; `m` is a pass-through.
-- Lowers via `Nat.rec`.
def myAdd : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (myAdd n m)

-- Three arguments, decreasing on the first; `m` and `k` are pass-throughs.
def add3 : Nat → Nat → Nat → Nat
  | 0, m, k => Nat.add m k
  | Nat.succ n, m, k => Nat.succ (add3 n m k)

-- Decreasing argument is the SECOND position; the leading `Nat` is a
-- pass-through bound *before* the decreasing arg (exercises the extra-param
-- machinery for binders that precede the decreasing one).
def appendR : Nat → Lst → Lst
  | h, Lst.nil => Lst.cons h Lst.nil
  | h, Lst.cons x t => Lst.cons x (appendR h t)

-- Computational checks: each `rfl` requires the kernel to reduce the recursive
-- `.rec` term, with the pass-through arguments threaded through the motive.

theorem app_nil   : Lst.append Lst.nil (Lst.cons 1 Lst.nil) = Lst.cons 1 Lst.nil := rfl
theorem app_one   : Lst.append (Lst.cons 5 Lst.nil) (Lst.cons 1 Lst.nil)
                      = Lst.cons 5 (Lst.cons 1 Lst.nil) := rfl
theorem app_two   : Lst.append (Lst.cons 5 (Lst.cons 6 Lst.nil)) (Lst.cons 1 Lst.nil)
                      = Lst.cons 5 (Lst.cons 6 (Lst.cons 1 Lst.nil)) := rfl

theorem add_0_5   : myAdd 0 5 = 5 := rfl
theorem add_2_3   : myAdd 2 3 = 5 := rfl
theorem add_4_4   : myAdd 4 4 = 8 := rfl

theorem add3_base : add3 0 2 3 = 5 := rfl
theorem add3_step : add3 2 3 4 = 9 := rfl

theorem appR_nil  : appendR 9 Lst.nil = Lst.cons 9 Lst.nil := rfl
theorem appR_one  : appendR 9 (Lst.cons 1 Lst.nil) = Lst.cons 1 (Lst.cons 9 Lst.nil) := rfl
theorem appR_two  : appendR 9 (Lst.cons 1 (Lst.cons 2 Lst.nil))
                      = Lst.cons 1 (Lst.cons 2 (Lst.cons 9 Lst.nil)) := rfl
