theorem opaque_refl_let_ok : True := by
  let h : Nat := 7
  have k : h = 7 := by rfl
  exact True.intro
