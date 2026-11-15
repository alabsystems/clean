theorem rwa_lemma_at_shadowed_positive (P : Nat → Prop) (a b c : Nat)
    (e : a = b) (e : a = c) (h : P a) : P c := by
  rwa [e] at h
