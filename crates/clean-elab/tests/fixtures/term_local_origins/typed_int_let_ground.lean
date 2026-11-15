theorem typed_int_let_ground : True :=
  let n : Int := 7
  have h : n = 7 := by rfl
  True.intro
#print axioms typed_int_let_ground
