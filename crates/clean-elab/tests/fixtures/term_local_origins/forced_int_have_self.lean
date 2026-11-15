theorem forced_int_have_self : True :=
  have n := 7
  have h : (n : Int) = n := by rfl
  True.intro
#print axioms forced_int_have_self
