-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

/-- Compiled code calls the C symbol; the kernel unfolds the body. -/
@[extern "clean_compiled_code_probe_extern"]
def CC.Extern.probe (n : Nat) : Nat := n
