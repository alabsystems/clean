theorem rwa_lemma_shadowed_negative (P : Nat → Prop) (a b c : Nat)
    (e : a = b) (e : a = c) (h : P b) : P a := by
  rwa [e]
