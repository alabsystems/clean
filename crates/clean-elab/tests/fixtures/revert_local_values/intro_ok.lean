theorem revert_let_intro_ok : True := by
  let x : Nat := 7
  revert x
  intro y
  have hy : y = 7 := rfl
  exact True.intro
