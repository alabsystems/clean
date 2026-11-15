theorem revert_let_retained_ok : True := by
  let h : True := True.intro
  revert h
  exact True.intro
