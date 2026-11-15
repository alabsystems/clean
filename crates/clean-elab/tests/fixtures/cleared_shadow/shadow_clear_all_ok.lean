theorem shadow_clear_all_ok (p q : Prop) (h : p) : q → True := by
  intro h
  clear h
  clear h
  exact True.intro
