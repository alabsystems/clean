theorem revert_let_intro_bad : True := by
  let x : Nat := 7
  revert x
  intro y
  have hy : y = 8 := rfl
  exact True.intro
