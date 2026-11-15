theorem opaque_have_exact_bad : True := by
  have h : Nat := 7
  have k : h = 7 := by exact Eq.refl 7
  exact True.intro
