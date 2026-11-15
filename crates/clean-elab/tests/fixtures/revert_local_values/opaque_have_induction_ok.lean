theorem opaque_dependency_have_induction_ok (b : Bool) : True := by
  have h : True := by
    cases b <;> exact True.intro
  induction b generalizing h <;> exact h
