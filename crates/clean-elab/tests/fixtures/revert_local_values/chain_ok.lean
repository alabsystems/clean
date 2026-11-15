theorem revert_let_chain_ok (n : Nat) : n = n := by
  let x : Nat := n
  let y : Nat := x
  revert x
  exact Eq.refl n
