-- Pinned open (G23 B3): Lean 4.8 states the catch-all arm's equation with
-- hypotheses; Clean does not mint it, so the name is unknown.
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
#check @P.beq.eq_3
