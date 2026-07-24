-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: equation-style `def` arms with full-expression bodies.
-- Before the parser fix, a def-match arm body was parsed atom-only, so any
-- body using an operator or a multi-argument pattern was silently truncated
-- (e.g. `| n => n + n` parsed as `n`). Arm bodies now parse as full
-- operator-precedence expressions, halting cleanly at the next `| pat =>`.
-- `clean check` accepts all of these and the `rfl` theorems confirm the bodies
-- elaborate to the intended expressions (not truncated ones).

-- single argument, operator body
def double : Nat → Nat
  | n => n + n

-- multiple arguments (comma-separated patterns), operator body
def addCases : Nat → Nat → Nat
  | 0, m => m
  | n, 0 => n
  | n, m => n + m

-- constructor patterns with an operator body
def pred2 : Nat → Nat
  | 0 => 0
  | Nat.succ n => n * 1

theorem double_3   : double 3 = 6 := rfl
theorem add_0_5    : addCases 0 5 = 5 := rfl
theorem add_3_0    : addCases 3 0 = 3 := rfl
theorem pred2_succ : pred2 (Nat.succ 4) = 4 := rfl
