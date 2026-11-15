theorem revert_let_selected_ok : True := by
  let x : Nat := 7
  revert x
  exact True.intro
