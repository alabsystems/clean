-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- A `partial` definition: an opaque constant whose compiled code is an unsafe
recursive body. -/
partial def CC.Partial.loop (n : Nat) : Nat := if n = 0 then 0 else CC.Partial.loop (n - 1)
