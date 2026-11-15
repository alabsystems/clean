inductive WrongReceiver : Nat → Prop where
  | intro {x} : x.length = 0 → WrongReceiver x
