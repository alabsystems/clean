-- Class (81) twin: `cases h` on `a :: as = b :: bs` identifies the heads,
-- it does not make `as` empty.
theorem ctor_inj_twin (a b : Nat) (as bs : List Nat) (h : a :: as = b :: bs) : as = [] := by
  cases h
  rfl
