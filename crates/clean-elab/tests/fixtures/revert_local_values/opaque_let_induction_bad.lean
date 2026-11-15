theorem opaque_dependency_let_induction_bad (b : Bool) : True := by
  let h : True := by
    cases b <;> exact True.intro
  induction b generalizing h <;> exact h
