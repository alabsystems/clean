theorem revert_let_dependent_ok : True := by
  let x : Nat := 7
  have h : x = x := by
    revert x
    intro y
    rfl
  exact True.intro
