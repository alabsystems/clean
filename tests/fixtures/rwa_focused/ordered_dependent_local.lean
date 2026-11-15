theorem rwa_ordered_dependent_local (P : Nat → Prop) (a : Nat)
    (h : P a) (b : Nat) (e : a = b) (hp : h = h) : P b := by
  rwa [e] at h
