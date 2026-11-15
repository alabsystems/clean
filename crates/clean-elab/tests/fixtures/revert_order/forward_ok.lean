theorem revert_forward_ok (p q : Prop) (hp : p) (hq : q) : p := by
  revert hp hq
  intro hp hq
  exact hp
