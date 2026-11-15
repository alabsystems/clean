-- G23 repro: mutual definitions over the nested inductive `P` (trust-ir
-- `Pred.beq` / `Pred.listBeq`, Pred.lean:346), checked by `decide`.
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

theorem t1 : P.beq (.conj [.leaf 1]) (.conj [.leaf 1]) = true := by decide
