-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- A plain definition and a theorem about it: nothing in this module changes
what compiled code runs. -/
def CC.Clean.double (n : Nat) : Nat := n + n

theorem CC.Clean.double_zero : CC.Clean.double 0 = 0 := rfl

/-- A well-founded recursive definition: Lean's compiler generates the partial copy
`CC.Clean.halve._unsafe_rec` from the same source and compiles `halve` from it, the one
`._unsafe_rec` the refusal allows. -/
def CC.Clean.halve (n : Nat) : Nat := if n < 2 then 0 else CC.Clean.halve (n - 2) + 1
termination_by n
decreasing_by omega
