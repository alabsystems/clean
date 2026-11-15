theorem shadow_rename_after_clear_bad (p q : Prop) (h : p) : q → p := by
  intro h
  clear h
  rename_i hp
  exact hp
