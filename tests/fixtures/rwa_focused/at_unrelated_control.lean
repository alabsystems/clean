theorem rwa_at_unrelated_control (a b c : Nat) (h : a = b) (target : a = c) (other : True) : True := by
  rw [h] at target
  exact other
