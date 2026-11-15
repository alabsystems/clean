theorem rwa_focus_leaves_sibling (a b : Nat) (h : a = b) (other : True) : (a = b) ∧ True := by
  constructor
  rwa [h]
