theorem rwa_conditional_open (P : Prop) (a b : Nat) (rule : P → a = b) : a = b := by
  rwa [rule]
