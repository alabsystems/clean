def let_mutable_if_value : Nat := Id.run do
  let mut x : Nat := 0
  if true then
    let h : True := True.intro
    x := 1
  return x

theorem let_mutable_if_ok : let_mutable_if_value = 1 := by rfl
#print axioms let_mutable_if_ok
