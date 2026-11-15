theorem opaque_nested_have_forbidden_bad (b : Bool) : True := by
  have h : Bool := b
  exact (by
    induction h generalizing b <;> exact True.intro)
