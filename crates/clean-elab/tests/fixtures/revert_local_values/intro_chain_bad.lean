theorem revert_let_intro_chain_bad (n : Nat) : True := by
  let x : Nat := n
  let y : Nat := x
  revert x
  intro a b
  have hab : a = Nat.succ b := rfl
  exact True.intro
