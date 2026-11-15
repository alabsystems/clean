theorem revert_have_parameter_ok : True := by
  have h : True := True.intro
  revert h
  exact (id : True → True)
