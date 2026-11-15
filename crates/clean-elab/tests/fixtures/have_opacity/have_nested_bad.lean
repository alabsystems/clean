theorem opaque_have_nested_bad : True := by
  have h : Nat := 7
  have k : h = 7 := by exact (by rfl)
  exact True.intro
