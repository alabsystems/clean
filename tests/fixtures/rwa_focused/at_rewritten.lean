theorem rwa_at_rewritten (a b c : Nat) (h : a = b) (target : a = c) : b = c := by
  rwa [h] at target
