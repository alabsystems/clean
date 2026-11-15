theorem opaque_let_term_ok : True := by
  let h : Nat := 7
  have k : h = 7 := rfl
  exact True.intro
