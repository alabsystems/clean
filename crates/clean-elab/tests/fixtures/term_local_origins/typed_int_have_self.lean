theorem typed_int_have_self : True :=
  have n : Int := 7
  have h : n = n := by rfl
  True.intro
#print axioms typed_int_have_self
