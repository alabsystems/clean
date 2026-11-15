theorem revert_let_intro_chain_ok (n : Nat) : True := by
  let x : Nat := n
  let y : Nat := x
  revert x
  intro a b
  have hab : a = b := rfl
  exact True.intro
