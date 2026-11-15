theorem rwa_at_refl (a b c : Nat) (h : a = b) (target : a = c) : b = b := by
  rwa [h] at target
