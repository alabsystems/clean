theorem rwa_conditional_closed (P : Prop) (a b : Nat) (rule : P → a = b) (h : P) : a = b := by
  rwa [rule]
