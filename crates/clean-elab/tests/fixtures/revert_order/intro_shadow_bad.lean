theorem intro_shadow_bad (p q : Prop) (h : p) : q → p := by
  intro h
  exact h
