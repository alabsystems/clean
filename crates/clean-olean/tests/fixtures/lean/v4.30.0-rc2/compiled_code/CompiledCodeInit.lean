-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- `initialize` runs an `IO` action when the program starts. -/
initialize CC.Init.probe : IO.Ref Nat ← IO.mkRef 0
