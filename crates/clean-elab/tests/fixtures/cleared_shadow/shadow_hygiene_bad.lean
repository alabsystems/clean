set_option quotPrecheck false
notation "SH " x => (by first | (clear h; exact 0) | exact x : Nat)
theorem shadow_hygiene_bad (h : Nat) (h : Nat) : (SH 1) = 0 := by rfl
