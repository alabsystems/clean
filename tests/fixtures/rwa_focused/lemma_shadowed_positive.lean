theorem rwa_lemma_shadowed_positive (P : Nat → Prop) (a b c : Nat)
    (e : a = b) (e : a = c) (h : P c) : P a := by
  rwa [e]
