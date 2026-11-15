theorem shadow_three_bad (p q r : Prop) (h : p) : q → r → p := by
  intro h
  intro h
  clear h
  exact h
