-- k1 w1: a defining equation on OPEN terms by `rfl`. Lean 4.8 refuses it
-- (its members are well-founded fixpoints that do not reduce on open terms);
-- Clean's structural members reduce: the recorded definitional widening.
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

theorem w1 (x y : List P) : P.beq (.conj x) (.conj y) = P.listBeq x y := rfl
