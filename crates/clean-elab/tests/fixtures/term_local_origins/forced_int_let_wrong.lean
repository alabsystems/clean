theorem forced_int_let_wrong : True :=
  let n := 7
  have h : (n : Int) = 8 := by rfl
  True.intro
#print axioms forced_int_let_wrong
