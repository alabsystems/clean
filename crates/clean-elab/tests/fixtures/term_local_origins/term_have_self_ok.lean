theorem term_have_self_ok : True :=
  have n : Nat := 7
  by
    have h : n = n := by rfl
    exact True.intro
#print axioms term_have_self_ok
