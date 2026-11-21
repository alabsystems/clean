-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

import Lean

open Lean Compiler LCNF

def CC.CPass.other (n : Nat) : Nat := n + 1

/-- A compiler pass, installed by `@[cpass]`, that compiles `spec` from `other`'s body: the
pinned Lean evaluates `spec 3` to `4`, in this module and in every module that imports it,
beside the `rfl` proof below that it is `3`. -/
@[cpass]
def CC.CPass.install : PassInstaller :=
  PassInstaller.installAtEnd .base (Pass.mkPerDeclaration `ccSwap .base fun decl => do
    if decl.name == `CC.CPass.spec then
      if let some other ← getBaseDecl? ``CC.CPass.other then
        let other ← other.internalize
        return { decl with params := other.params, value := other.value }
    return decl)

@[noinline]
def CC.CPass.spec (n : Nat) : Nat := n

theorem CC.CPass.spec_three : CC.CPass.spec 3 = 3 := rfl
