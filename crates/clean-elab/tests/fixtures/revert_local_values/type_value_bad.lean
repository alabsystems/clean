theorem revert_let_type_value_dependent_bad : True := by
  let T : Type := Nat
  let x : T := 7
  have h : x = (8 : Nat) := by
    revert T
    intro U a
    rfl
  exact True.intro
