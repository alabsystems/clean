-- Soundness gate: universe level mismatch
-- Expected: clean and Lean 4 both reject
-- Sort 2 is not Sort 0 (Prop), so this definition has a type mismatch.

def bad_sort : Prop := Sort 2
