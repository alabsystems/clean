def have_mutable_if_value : Nat := Id.run do
  let mut x : Nat := 0
  if true then
    have h : True := True.intro
    x := 1
  return x

theorem have_mutable_if_ok : have_mutable_if_value = 1 := by rfl
#print axioms have_mutable_if_ok
