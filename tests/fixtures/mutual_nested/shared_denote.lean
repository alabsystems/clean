-- Brick B2 (judge k3): trust-ir `Pred.denote` / `denoteAll` / `denoteAny`
-- (Pred.lean:396) — a fixed parameter `k`, a trailing `v`, codomain
-- `Nat → Prop`, and `List Q` owned twice. `:= True.intro` / `:= id` reduce
-- through the `PProd` slot with `v` open.
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
theorem dt (k v : Nat) : Q.denote k .top v := True.intro
theorem db (k v : Nat) : ¬ Q.denote k .bot v := id
theorem dc (k v : Nat) : Q.denote k (.conj []) v := True.intro
