theorem revert_transitive_dep_bad (n : Nat) (h : n = 0) (hh : h = h) : n = 0 := by
  revert n
  intro n h hh
  rfl
