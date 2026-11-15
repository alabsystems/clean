theorem revert_let_ordinary_ok (n : Nat) : n = n := by
  revert n
  exact fun k => Eq.refl k
