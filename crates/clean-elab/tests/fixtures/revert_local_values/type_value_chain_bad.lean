theorem revert_let_type_value_chain_dependent_bad (n : Nat) : True := by
  let T : Type := Nat
  let x : T := n
  let y : T := x
  have h : y = Nat.succ n := by
    revert T
    intro U a b
    rfl
  exact True.intro
