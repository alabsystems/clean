theorem rwa_shadowed_negative (a b : Nat) (e : a = b)
    (h : a = a) (h : a = b) : a = b := by
  rwa [e] at h
