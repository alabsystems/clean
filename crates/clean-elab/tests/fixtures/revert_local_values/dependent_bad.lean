theorem revert_let_dependent_bad : True := by
  let x : Nat := 7
  have h : x = 8 := by
    revert x
    intro y
    rfl
  exact True.intro
