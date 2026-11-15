-- Twin of eqns_simp.lean (judge k1 s1f): the false equation simp must not close.
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
theorem s1f (x y : List P) : P.beq (.conj x) (.conj y) = !P.listBeq x y := by simp [P.beq]
