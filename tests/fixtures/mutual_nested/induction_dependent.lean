-- Gap G22: `induction x` generalizes every hypothesis that mentions `x`
-- together with the `generalizing` variables, in context order, so the
-- induction hypothesis carries them as premises.
theorem ih_uses_dep (xs : List Nat) (h : xs = []) : xs.length = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases h

theorem ih_order (xs : List Nat) (n : Nat) (h0 : xs.length = n) : xs.length = n := by
  induction xs generalizing n with
  | nil => exact h0
  | cons x rest ih =>
    have hi := ih rest.length rfl
    exact h0

theorem no_with (xs : List Nat) (h : xs.length = 0) : xs.length = 0 := by
  induction xs
  · rfl
  · exact h

theorem with_ctor_eq (xs : List Nat) (c : Nat) (hc : c ∈ xs) (h0 : xs = []) : xs.length = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases h0
