theorem revert_let_selected_bad : 7 = 8 := by
  let x : Nat := 7
  revert x
  exact Eq.refl 7
