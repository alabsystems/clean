theorem let_for_local_equation_wrong : True :=
  let computed : Nat := Id.run do
    let mut x : Nat := 0
    for _ in [0, 1] do
      let h : True := True.intro
      x := x + 1
    return x
  have checked : computed = 1 := by rfl
  True.intro
#print axioms let_for_local_equation_wrong
