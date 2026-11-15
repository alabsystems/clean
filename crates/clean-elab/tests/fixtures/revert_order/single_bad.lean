theorem revert_single_bad (p q : Prop) (hp : p) (hq : q) : p := by
  revert hp
  intro hp
  exact hq
