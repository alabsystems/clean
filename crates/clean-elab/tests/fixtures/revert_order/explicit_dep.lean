theorem revert_explicit_dep (n : Nat) (h : n = 0) : n = 0 := by
  revert n h
  intro n h
  exact h
