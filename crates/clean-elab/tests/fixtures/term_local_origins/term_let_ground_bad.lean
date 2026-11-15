theorem term_let_ground_bad : True :=
  let n : Nat := 7
  by
    have h : n = 8 := by rfl
    exact True.intro
#print axioms term_let_ground_bad
