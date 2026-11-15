theorem revert_explicit_dep_bad (n : Nat) (h : n = 0) : n = 0 := by
  revert n h
  intro n h
  rfl
