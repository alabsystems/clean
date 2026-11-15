-- Twin of eqns_simp.lean s2: the hypothesis says nothing about the tails' heads.
inductive P where
  | leaf : Nat → P
  | conj : List P → P
mutual
def P.beq : P → P → Bool
  | .leaf a, .leaf b => a == b
  | .conj x, .conj y => P.listBeq x y
  | _, _ => false
def P.listBeq : List P → List P → Bool
  | [], [] => true
  | p :: ps, q :: qs => P.beq p q && P.listBeq ps qs
  | _, _ => false
end
theorem s2f (p q : P) (ps qs : List P) (h : P.listBeq (p :: ps) (q :: qs) = true) : P.beq q p = false := by
  simp only [P.listBeq, Bool.and_eq_true] at h
  exact h.1
