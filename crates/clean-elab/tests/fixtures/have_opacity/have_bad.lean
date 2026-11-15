theorem opaque_refl_have_bad : True := by
  have h : Nat := 7
  have k : h = 7 := by rfl
  exact True.intro
