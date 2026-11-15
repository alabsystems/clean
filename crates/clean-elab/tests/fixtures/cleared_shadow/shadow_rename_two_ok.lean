theorem shadow_rename_two_ok (p q r : Prop) (h : p) : q → r → p := by
  intro h
  intro h
  rename_i hp hq
  exact hp
