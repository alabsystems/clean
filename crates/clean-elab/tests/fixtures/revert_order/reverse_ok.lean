theorem revert_reverse_ok (p q : Prop) (hp : p) (hq : q) : p := by
  revert hq hp
  intro hp hq
  exact hp
