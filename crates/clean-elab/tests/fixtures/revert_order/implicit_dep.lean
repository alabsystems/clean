theorem revert_implicit_dep (n : Nat) (h : n = 0) : n = 0 := by
  revert n
  intro n h
  exact h
