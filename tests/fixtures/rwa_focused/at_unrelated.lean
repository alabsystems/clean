theorem rwa_at_unrelated (a b c : Nat) (h : a = b) (target : a = c) (other : True) : True := by
  rwa [h] at target
