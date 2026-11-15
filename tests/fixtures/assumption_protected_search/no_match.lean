@[irreducible] def assumption_carrier : Type := Nat
def no_match (blocked : assumption_carrier) : Nat := by
  assumption
