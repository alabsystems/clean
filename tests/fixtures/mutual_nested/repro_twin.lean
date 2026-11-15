-- G23 negative twin: the same block, a FALSE closed claim.
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

theorem t1_twin : P.beq (.conj [.leaf 1]) (.conj [.leaf 2]) = true := by decide
