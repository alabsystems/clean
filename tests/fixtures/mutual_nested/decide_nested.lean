-- k1 d2: decide through two nesting levels and both list arms.
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

theorem d2 : P.beq (.conj [.leaf 1, .conj []]) (.conj [.leaf 1, .conj []]) = true := by decide
