-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- A negative control of the compiled-checker refusal (crates/clean-olean/tests/compiled_code.rs).

def CC.CSimp.slow (n : Nat) : Nat := n

def CC.CSimp.quick (n : Nat) : Nat := n

/-- The code generator replaces `slow` by `quick` everywhere. -/
@[csimp]
theorem CC.CSimp.slow_eq_quick : @CC.CSimp.slow = @CC.CSimp.quick := rfl
