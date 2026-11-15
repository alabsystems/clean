theorem inferred_nat_let_ground : True :=
  let n := 7
  have h : n = 7 := by rfl
  True.intro
#print axioms inferred_nat_let_ground
