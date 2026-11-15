theorem opaque_refl_let_bad : True := by
  let h : Nat := 7
  have k : h = 8 := by rfl
  exact True.intro
