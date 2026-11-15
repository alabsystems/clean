-- B5 twin: a false claim over the nested `P`; both cases elaborate, the
-- `conj` one cannot close.
inductive P where
  | leaf : Nat → P
  | conj : List P → P

def P.isLeaf : P → Bool
  | .leaf _ => true
  | .conj _ => false

theorem with_alts_twin (p : P) : p.isLeaf = true := by
  cases p with
  | leaf n => rfl
  | conj xs => rfl
