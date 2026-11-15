theorem revert_let_type_value_dependent_ok : True := by
  let T : Type := Nat
  let x : T := 7
  have h : x = (7 : Nat) := by
    revert T
    intro U a
    rfl
  exact True.intro
