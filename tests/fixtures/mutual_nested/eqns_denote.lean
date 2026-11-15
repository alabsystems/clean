-- Gap G23 brick B3 (judge k3 e2): `rw [f.eq_N]` on a shared-slot member (the
-- Pred.denote shape); each statement is ascribed exactly as Lean 4.8's `#check` prints it.
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
theorem e2 (k v : Nat) (cs : List Q) : Q.denote k (.disj cs) v = Q.denoteAny k cs v := by rw [Q.denote.eq_4]
theorem q1 : ∀ (k x : Nat), Q.denote k Q.top x = True := Q.denote.eq_1
theorem q2 : ∀ (k x : Nat), Q.denote k Q.bot x = False := Q.denote.eq_2
theorem q3 : ∀ (k x : Nat) (cs : List Q), Q.denote k (Q.conj cs) x = Q.denoteAll k cs x := Q.denote.eq_3
theorem q4 : ∀ (k x : Nat) (cs : List Q), Q.denote k (Q.disj cs) x = Q.denoteAny k cs x := Q.denote.eq_4
theorem q5 : ∀ (k x : Nat), Q.denoteAll k [] x = True := Q.denoteAll.eq_1
theorem q6 : ∀ (k x : Nat) (p : Q) (r : List Q), Q.denoteAll k (p :: r) x = (Q.denote k p x ∧ Q.denoteAll k r x) := Q.denoteAll.eq_2
theorem q7 : ∀ (k x : Nat) (p : Q) (r : List Q), Q.denoteAny k (p :: r) x = (Q.denote k p x ∨ Q.denoteAny k r x) := Q.denoteAny.eq_2
theorem g1 (v : Nat) : Q.denote 0 (.conj []) v := by simp [Q.denote, Q.denoteAll]
theorem g2 (v : Nat) : Q.denote 0 (.disj [.top]) v := by simp [Q.denote, Q.denoteAny]
