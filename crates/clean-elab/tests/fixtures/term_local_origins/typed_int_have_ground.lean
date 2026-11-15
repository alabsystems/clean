theorem typed_int_have_ground : True :=
  have n : Int := 7
  have h : n = 7 := by rfl
  True.intro
#print axioms typed_int_have_ground
