theorem revert_have_retained_bad : True := by
  have h : True := True.intro
  revert h
  exact True.intro
