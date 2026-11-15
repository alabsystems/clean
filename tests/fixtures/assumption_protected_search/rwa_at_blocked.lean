@[irreducible] def assumption_carrier : Type := Nat
def rwa_at_blocked (good : Nat) (blocked : assumption_carrier) : Nat := by
  rwa [] at blocked
