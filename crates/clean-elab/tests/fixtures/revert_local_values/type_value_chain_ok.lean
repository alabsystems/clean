theorem revert_let_type_value_chain_dependent_ok (n : Nat) : True := by
  let T : Type := Nat
  let x : T := n
  let y : T := x
  have h : y = n := by
    revert T
    intro U a b
    rfl
  exact True.intro
