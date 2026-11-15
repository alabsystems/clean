theorem revert_transitive_dep (n : Nat) (h : n = 0) (hh : h = h) : n = 0 := by
  revert n
  intro n h hh
  exact h
