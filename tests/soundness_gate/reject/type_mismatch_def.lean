-- Soundness gate: value type does not match declared type
-- Expected: clean and Lean 4 both reject
-- Type is Sort 1, not Sort 0 (Prop).

def bad_level : Prop := Type
