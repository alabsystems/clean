-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: Clean's elaborator + kernel verify a trust-ir-shaped IR-semantics
-- slice end to end. Every declaration here FAILED before the trust-ir-support
-- elaborator fixes (equational `rfl` universe pinning, hetero-arithmetic
-- typeclasses for `-`/`*`, inductive `deriving Repr`). `clean check` accepts all.
inductive BinOp where
  | Add
  | Sub
  | Mul
  deriving Repr

def semBinOp (op : BinOp) (l r : Nat) : Nat :=
  match op with
  | BinOp.Add => l + r
  | BinOp.Sub => l - r
  | BinOp.Mul => l * r

theorem sem_add        : semBinOp BinOp.Add 2 3 = 5 := rfl
theorem sem_sub        : semBinOp BinOp.Sub 5 2 = 3 := rfl
theorem sem_mul        : semBinOp BinOp.Mul 4 2 = 8 := rfl
theorem sem_add_param (l r : Nat) : semBinOp BinOp.Add l r = l + r := rfl
theorem sem_sub_param (l r : Nat) : semBinOp BinOp.Sub l r = l - r := by rfl
