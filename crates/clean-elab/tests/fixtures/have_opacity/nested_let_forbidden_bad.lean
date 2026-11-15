theorem opaque_nested_let_forbidden_bad (b : Bool) : True := by
  let h : Bool := b
  exact (by
    induction h generalizing b <;> exact True.intro)
