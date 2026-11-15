theorem inferred_nat_let_wrong : True :=
  let n := 7
  have h : n = 8 := by rfl
  True.intro
#print axioms inferred_nat_let_wrong
