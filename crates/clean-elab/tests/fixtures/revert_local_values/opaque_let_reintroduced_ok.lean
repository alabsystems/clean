theorem opaque_dependency_let_reintroduced_ok (b : Bool) : True := by
  let h : True := by
    cases b <;> exact True.intro
  revert b
  intro b
  intro h
  exact h
