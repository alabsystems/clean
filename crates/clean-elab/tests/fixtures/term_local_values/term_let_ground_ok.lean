theorem term_let_ground_ok : True :=
  let n : Nat := 7
  by
    have h : n = 7 := by rfl
    exact True.intro
#print axioms term_let_ground_ok
