-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- Compiled code runs the value; no kernel theorem can depend on it. -/
opaque CC.Opaque.hidden : Nat → Nat := fun n => n + 1
