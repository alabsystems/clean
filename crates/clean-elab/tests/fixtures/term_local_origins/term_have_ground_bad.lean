theorem term_have_ground_bad : True :=
  have n : Nat := 7
  by
    have h : n = 7 := by rfl
    exact True.intro
#print axioms term_have_ground_bad
