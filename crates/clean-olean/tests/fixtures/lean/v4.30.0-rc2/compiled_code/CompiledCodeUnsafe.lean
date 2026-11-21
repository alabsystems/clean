-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- An `unsafe` definition: never checked by the kernel. -/
unsafe def CC.Unsafe.raw (n : Nat) : Nat := n
