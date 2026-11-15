theorem revert_single_ok (p q : Prop) (hp : p) (hq : q) : p := by
  revert hp
  intro hp
  exact hp
