theorem opaque_dependency_have_parameter_bad (b : Bool) : True := by
  have h : True := by
    cases b <;> exact True.intro
  revert b
  exact fun _ h => h
