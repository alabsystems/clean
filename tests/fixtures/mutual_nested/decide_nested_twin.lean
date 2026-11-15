-- k1 d2f: the false twin of decide_nested.
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

theorem d2f : P.beq (.conj [.leaf 1, .conj []]) (.conj [.leaf 1, .conj [.leaf 0]]) = true := by decide
