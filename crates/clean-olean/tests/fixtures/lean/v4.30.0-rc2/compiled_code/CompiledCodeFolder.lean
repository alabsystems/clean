-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

import Lean

open Lean Compiler LCNF Simp ConstantFold

@[noinline]
def CC.Folder.spec (n : Nat) : Nat := n

/-- A constant folder for `spec`: the code generator folds `spec k`, for a literal `k`, to
`k + 1`. -/
def CC.Folder.fold : Folder := Folder.mkUnary fun (k : Nat) => k + 1

run_meta registerFolder ``CC.Folder.spec ``CC.Folder.fold

theorem CC.Folder.spec_three : CC.Folder.spec 3 = 3 := rfl

/-- The pinned Lean compiles `use` to the literal `4`, in this module and in every module that
imports it. -/
def CC.Folder.use (_ : Unit) : Nat := CC.Folder.spec 3
