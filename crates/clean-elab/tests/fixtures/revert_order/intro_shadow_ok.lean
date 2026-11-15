theorem intro_shadow_ok (p q : Prop) (h : p) : q → q := by
  intro h
  exact h
