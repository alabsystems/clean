set_option quotPrecheck false
notation "SH " x => (by first | (clear h; exact 0) | exact x : Nat)
theorem shadow_hygiene_ok (h : Nat) (h : Nat) : (SH 1) = 1 := by rfl
