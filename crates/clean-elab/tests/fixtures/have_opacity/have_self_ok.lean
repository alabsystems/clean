theorem opaque_refl_have_self_ok : True := by
  have h : Nat := 7
  have k : h = h := by rfl
  exact True.intro
