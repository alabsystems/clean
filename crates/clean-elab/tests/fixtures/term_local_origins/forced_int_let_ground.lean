theorem forced_int_let_ground : True :=
  let n := 7
  have h : (n : Int) = 7 := by rfl
  True.intro
#print axioms forced_int_let_ground
