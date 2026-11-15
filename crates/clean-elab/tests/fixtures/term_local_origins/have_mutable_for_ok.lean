def have_mutable_for_value : Nat := Id.run do
  let mut x : Nat := 0
  for _ in [0, 1] do
    have h : True := True.intro
    x := x + 1
  return x

theorem have_mutable_for_ok : have_mutable_for_value = 2 := by rfl
#print axioms have_mutable_for_ok
