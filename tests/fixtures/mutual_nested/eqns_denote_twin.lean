-- Twin of eqns_denote.lean (judge k3 e2f): eq_4 is the disjunction arm.
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
theorem e2f (k v : Nat) (cs : List Q) : Q.denote k (.disj cs) v = Q.denoteAll k cs v := by rw [Q.denote.eq_4]
