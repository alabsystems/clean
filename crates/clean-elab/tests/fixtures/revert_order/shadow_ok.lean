theorem revert_shadow_ok (p q : Prop) (h : p) (h : q) : q := by
  revert h
  intro h
  exact h
