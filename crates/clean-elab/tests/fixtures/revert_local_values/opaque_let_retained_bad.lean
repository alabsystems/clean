theorem opaque_dependency_let_retained_bad (b : Bool) : True := by
  let h : True := by
    cases b <;> exact True.intro
  revert b
  exact fun _ => h
