theorem revert_let_value_chain_dependent_ok (n : Nat) : True := by
  let x : Nat := n
  let y : Nat := x
  have h : y = n := by
    revert x
    intro a b
    rfl
  exact True.intro
