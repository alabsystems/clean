theorem rwa_focus_keeps_sibling (a b : Nat) (h : a = b) (other : True) : (a = b) ∧ True := by
  constructor
  rwa [h]
  exact other
