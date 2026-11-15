inductive HeaderIndex (p : α → Prop) : Nat → Prop where
  | zero : HeaderIndex p 0
def badIndex : HeaderIndex (fun n : Nat => n = 0) 1 := HeaderIndex.zero
