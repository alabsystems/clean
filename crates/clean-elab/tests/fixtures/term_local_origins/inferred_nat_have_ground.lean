theorem inferred_nat_have_ground : True :=
  have n := 7
  have h : n = 7 := by rfl
  True.intro
#print axioms inferred_nat_have_ground
