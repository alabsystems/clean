theorem revert_let_chain_bad (n : Nat) : n = 0 := by
  let x : Nat := n
  let y : Nat := x
  revert x
  exact Eq.refl n
