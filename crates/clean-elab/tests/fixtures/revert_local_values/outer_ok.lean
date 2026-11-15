theorem revert_let_outer_ok (n : Nat) : n = n := by
  let x : Nat := n
  revert n
  intro k
  exact Eq.refl k
