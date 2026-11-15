theorem rwa_shadowed_positive (P Q : Nat → Prop) (a b : Nat)
    (e : a = b) (h : Q a) (h : P a) : P b := by
  rwa [e] at h
