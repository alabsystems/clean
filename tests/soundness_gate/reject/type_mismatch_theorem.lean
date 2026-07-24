-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0

-- Soundness gate: value type does not match declared type
-- Expected: clean and Lean 4 both reject
-- Type is Sort 1, not Sort 0 (Prop).

theorem bad_level_theorem : Prop := Type
