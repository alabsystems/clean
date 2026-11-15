theorem revert_shadow_bad (p q : Prop) (h : p) (h : q) : p := by
  revert h
  intro h
  exact h
