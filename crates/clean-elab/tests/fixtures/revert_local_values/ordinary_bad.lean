theorem revert_let_ordinary_bad (n : Nat) : n = 0 := by
  revert n
  exact fun k => Eq.refl k
