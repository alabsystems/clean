theorem revert_let_parameter_bad : True := by
  let h : True := True.intro
  revert h
  exact (id : True → True)
