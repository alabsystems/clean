theorem revert_let_cases_bad (b : Bool) : b = b := by
  let x : Bool := b
  cases b
  · exact (show x = Bool.false from rfl)
  · exact (show x = Bool.false from rfl)
