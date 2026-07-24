-- Soundness gate: applying a non-function
-- Expected: clean and Lean 4 both reject
-- Prop is not a function; applying it to Type is ill-typed.

axiom P : Prop
def bad := P Type
