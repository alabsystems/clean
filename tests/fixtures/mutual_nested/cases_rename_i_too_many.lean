-- Gap G67: `rename_i` with more names than inaccessible locals is refused
-- ("too many variable names provided").
theorem rename_none (a b : Nat) (h : a = b) : b = a := by
  revert h
  intro h'
  rename_i x
  exact h'.symm

