theorem rwa_lemma_shadowed_term_control (P : Nat → Prop) (a b c : Nat)
    (e : a = b) (e : a = c) (h : P c) : P a := by
  rwa [show a = c from e]
