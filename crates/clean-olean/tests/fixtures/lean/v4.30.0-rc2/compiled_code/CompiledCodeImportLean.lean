-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

import Lean

open Lean Elab Command

def CC.ImportLean.spec (n : Nat) : Nat := n

/- A metaprogram adds a partial `spec._unsafe_rec` whose body is `n + 1` and compiles it: Lean's
code generator compiles `spec` from it, so the pinned Lean evaluates `spec 3` to `4`, in this
module and in every module that imports it, beside the `rfl` proof below that it is `3`. The
compiled data holds a safe `spec` and a partial `spec._unsafe_rec` in one module, the shape of
the compiler's own copy, so only the import of `Lean` is refused. -/
run_cmd liftTermElabM do
  let type := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)
  let value := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  addDecl (.defnDecl {
    name := `CC.ImportLean.spec._unsafe_rec, levelParams := [], type, value,
    hints := .opaque, safety := .partial })
  compileDecls #[`CC.ImportLean.spec._unsafe_rec]

theorem CC.ImportLean.spec_three : CC.ImportLean.spec 3 = 3 := rfl
