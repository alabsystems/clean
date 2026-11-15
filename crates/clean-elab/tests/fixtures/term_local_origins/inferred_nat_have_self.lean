theorem inferred_nat_have_self : True :=
  have n := 7
  have h : n = n := by rfl
  True.intro
#print axioms inferred_nat_have_self
