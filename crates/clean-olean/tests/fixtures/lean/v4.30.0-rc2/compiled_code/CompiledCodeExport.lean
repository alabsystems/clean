-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- The compiled function is emitted under a C symbol other code can link to. -/
@[export clean_compiled_code_probe_export]
def CC.Export.probe (n : Nat) : Nat := n
