theorem revert_let_value_chain_dependent_bad (n : Nat) : True := by
  let x : Nat := n
  let y : Nat := x
  have h : y = Nat.succ n := by
    revert x
    intro a b
    rfl
  exact True.intro
