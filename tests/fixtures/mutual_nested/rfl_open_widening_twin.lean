-- k1 w1f: the false twin of rfl_open_widening, refused by both.
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

theorem w1f (x y : List P) : P.beq (.conj x) (.conj y) = !P.listBeq x y := rfl
