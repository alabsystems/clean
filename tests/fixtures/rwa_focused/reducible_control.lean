def rwa_hidden (n : Nat) : Nat := n
theorem rwa_reducible_control (a b : Nat) (h : a = b) : rwa_hidden a = b := by
  rw [h]
  rfl
