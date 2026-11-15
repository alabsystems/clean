-- Brick B2 (judge j2_denote): the trust-ir `Pred.denote` block shape —
-- fixed `U m`, an inner `match U` in an arm, `List P` owned twice —
-- with `denote_Top := True.intro` at `U m v` open.
inductive P where
  | Interval : Int → Int → P
  | NonZero : P
  | Conj : List P → P
  | Disj : List P → P
  | Top : P
  | Bottom : P

mutual
def P.denote (U : List Nat) (m : Nat → Int → Prop) : P → Int → Prop
  | .Interval lo hi, v => lo ≤ v ∧ v ≤ hi
  | .NonZero, v =>
    match U with
    | [] => False
    | k :: _ => m k v
  | .Conj cs, v => P.denoteAll U m cs v
  | .Disj cs, v => P.denoteAny U m cs v
  | .Top, _ => True
  | .Bottom, _ => False
def P.denoteAll (U : List Nat) (m : Nat → Int → Prop) : List P → Int → Prop
  | [], _ => True
  | p :: rest, v => P.denote U m p v ∧ P.denoteAll U m rest v
def P.denoteAny (U : List Nat) (m : Nat → Int → Prop) : List P → Int → Prop
  | [], _ => False
  | p :: rest, v => P.denote U m p v ∨ P.denoteAny U m rest v
end
theorem denote_Top (U : List Nat) (m : Nat → Int → Prop) (v : Int) : P.denote U m .Top v := True.intro
theorem denote_Conj_nil (U : List Nat) (m : Nat → Int → Prop) (v : Int) :
    P.denote U m (.Conj []) v := True.intro
