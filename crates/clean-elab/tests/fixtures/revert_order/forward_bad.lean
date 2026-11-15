theorem revert_forward_bad (p q : Prop) (hp : p) (hq : q) : p := by
  revert hp hq
  intro hp hq
  exact hq
