theorem forced_int_have_ground : True :=
  have n := 7
  have h : (n : Int) = 7 := by rfl
  True.intro
#print axioms forced_int_have_ground
