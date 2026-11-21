-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

def CC.ImplementedBy.fast (n : Nat) : Nat := n + 1

/-- Compiled code runs `fast` wherever it calls `spec`; the kernel unfolds `spec`. -/
@[implemented_by CC.ImplementedBy.fast]
def CC.ImplementedBy.spec (n : Nat) : Nat := n
