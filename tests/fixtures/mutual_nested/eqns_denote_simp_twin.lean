-- Mis-wiring control for `simp [f]` (shared_neg): an empty disjunction is false.
inductive Q where
  | top : Q
  | bot : Q
  | conj : List Q → Q
  | disj : List Q → Q
mutual
def Q.denote (k : Nat) : Q → Nat → Prop
  | .top, _ => True
  | .bot, _ => False
  | .conj cs, v => Q.denoteAll k cs v
  | .disj cs, v => Q.denoteAny k cs v
def Q.denoteAll (k : Nat) : List Q → Nat → Prop
  | [], _ => True
  | p :: r, v => Q.denote k p v ∧ Q.denoteAll k r v
def Q.denoteAny (k : Nat) : List Q → Nat → Prop
  | [], _ => False
  | p :: r, v => Q.denote k p v ∨ Q.denoteAny k r v
end
theorem bad (v : Nat) : Q.denote 0 (.disj []) v := by simp [Q.denote, Q.denoteAny, Q.denoteAll]
