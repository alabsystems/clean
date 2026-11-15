theorem opaque_nested_have_induction_ok (b : Bool) : True := by
  have h : Bool := b
  exact (by
    induction h <;> exact True.intro)
