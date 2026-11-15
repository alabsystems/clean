theorem opaque_let_nested_ok : True := by
  let h : Nat := 7
  have k : h = 7 := by exact (by rfl)
  exact True.intro
