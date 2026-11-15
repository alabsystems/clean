theorem revert_let_outer_bad (n : Nat) : n = 0 := by
  let x : Nat := n
  revert n
  intro k
  exact Eq.refl k
