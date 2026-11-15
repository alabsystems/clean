theorem have_for_local_equation_ok : True :=
  let computed : Nat := Id.run do
    let mut x : Nat := 0
    for _ in [0, 1] do
      have h : True := True.intro
      x := x + 1
    return x
  have checked : computed = 2 := by rfl
  True.intro
#print axioms have_for_local_equation_ok
