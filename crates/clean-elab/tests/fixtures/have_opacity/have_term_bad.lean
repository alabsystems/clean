theorem opaque_have_term_bad : True := by
  have h : Nat := 7
  have k : h = 7 := rfl
  exact True.intro
