-- Twin: no equation eliminates `r` (Lean: "did not find equation for
-- eliminating 'r'").
theorem sv_twin (p q r : Nat) (h : p = q) : r = r := by
  subst r
  rfl
