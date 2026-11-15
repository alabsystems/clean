theorem shadow_rename_old_ok (p q : Prop) (h : p) : q → p := by
  intro h
  rename_i hp
  exact hp
