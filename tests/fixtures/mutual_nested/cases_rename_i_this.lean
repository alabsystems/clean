-- Gap G67: `this` is accessible, so `rename_i` has nothing to name here
-- ("too many variable names provided").
theorem rename_this (p : Nat) (h : True) : True := by
  have : p = p := rfl
  rename_i z
  trivial
