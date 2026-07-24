-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: equation-style RECURSIVE `def`s lowered to the inductive's
-- `.rec` eliminator (Task 3, slice 1).
--
-- Before this change, an equation-form recursive def such as
--   `def factorial : Nat → Nat | 0 => 1 | Nat.succ n => ... factorial n`
-- failed to elaborate: the parser desugars the arms into a value
-- `PatternMatchLambda([_x], match _x ...)` with an empty declaration-binder
-- list (the `Nat → Nat` lives in the type), so the recursion machinery never
-- resolved a decreasing argument and the self-name `factorial` was left as a
-- `Nat`-typed placeholder — `factorial n` over-applied (`TooManyArguments`).
--
-- Clean now normalizes the equation form into the named-binder + `match` shape,
-- so single-argument structural recursion lowers through the inductive's `.rec`
-- (genuine structural recursion — no faked termination). `clean check` accepts
-- these defs and the `rfl` theorems force the kernel to fully reduce the `.rec`
-- applications, confirming the lowered terms compute the intended values.

-- Structural recursion on `Nat`, lowered via `Nat.rec`.
def factorial : Nat → Nat
  | 0 => 1
  | Nat.succ n => Nat.mul (Nat.succ n) (factorial n)

-- Structural recursion on a SECOND inductive (`List`), lowered via `List.rec`.
def listLen : List Nat → Nat
  | List.nil => 0
  | List.cons _ t => Nat.succ (listLen t)

-- Computational checks: each `rfl` requires the kernel to reduce the recursive
-- `.rec` term to a numeral.
theorem fac_0 : factorial 0 = 1 := rfl
theorem fac_1 : factorial 1 = 1 := rfl
theorem fac_3 : factorial 3 = 6 := rfl
theorem fac_4 : factorial 4 = 24 := rfl

theorem len_nil  : listLen List.nil = 0 := rfl
theorem len_one  : listLen (List.cons 7 List.nil) = 1 := rfl
theorem len_two  : listLen (List.cons 7 (List.cons 9 List.nil)) = 2 := rfl
