theorem opaque_let_exact_ok : True := by
  let h : Nat := 7
  have k : h = 7 := by exact Eq.refl 7
  exact True.intro
