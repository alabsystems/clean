theorem typed_int_let_wrong : True :=
  let n : Int := 7
  have h : n = 8 := by rfl
  True.intro
#print axioms typed_int_let_wrong
