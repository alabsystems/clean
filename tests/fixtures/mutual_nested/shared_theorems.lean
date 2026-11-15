-- Brick B2, shared slot in a THEOREM block: two theorems own `List Q`, so
-- the `Prop` motive of that slot is an `And` pair.
inductive Q where
  | top : Q
  | conj : List Q → Q
  | disj : List Q → Q
mutual
theorem Q.r : ∀ q : Q, True
  | .top => True.intro
  | .conj cs => Q.ra cs
  | .disj cs => Q.rb cs
theorem Q.ra : ∀ cs : List Q, True
  | [] => True.intro
  | p :: ps => (fun _ _ => True.intro) (Q.r p) (Q.ra ps)
theorem Q.rb : ∀ cs : List Q, True
  | [] => True.intro
  | p :: ps => (fun _ _ => True.intro) (Q.r p) (Q.rb ps)
end
