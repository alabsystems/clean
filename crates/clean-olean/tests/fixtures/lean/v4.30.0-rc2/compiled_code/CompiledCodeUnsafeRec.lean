-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

def CC.UnsafeRec.spec (n : Nat) : Nat := n

/-- Lean's code generator compiles `spec` from a constant of this name, so compiled code
runs `n + 1` wherever it calls `spec`, while the kernel unfolds `spec` to `n`. -/
def CC.UnsafeRec.spec._unsafe_rec (n : Nat) : Nat := n + 1

theorem CC.UnsafeRec.spec_three : CC.UnsafeRec.spec 3 = 3 := rfl
