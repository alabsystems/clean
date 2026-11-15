def let_mutable_for_value : Nat := Id.run do
  let mut x : Nat := 0
  for _ in [0, 1] do
    let h : True := True.intro
    x := x + 1
  return x

theorem let_mutable_for_ok : let_mutable_for_value = 2 := by rfl
#print axioms let_mutable_for_ok
