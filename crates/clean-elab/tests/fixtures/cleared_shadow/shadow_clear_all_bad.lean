theorem shadow_clear_all_bad (p q : Prop) (h : p) : q → p := by
  intro h
  clear h
  clear h
  exact h
