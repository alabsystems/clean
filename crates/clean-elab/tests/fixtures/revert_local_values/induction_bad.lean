theorem revert_let_induction_bad (n : Nat) : True := by
  let x : Nat := n
  induction n with
  | zero =>
    have hx : x = 0 := rfl
    exact True.intro
  | succ k ih =>
    have hx : x = 0 := rfl
    exact True.intro
