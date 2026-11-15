-- Refused by Lean 4.8: `P.f (.conj (p :: ps))` rebuilds the major premise.
inductive P where
  | leaf : Nat → P
  | conj : List P → P
mutual
def P.f : P → Nat
  | .leaf n => n
  | .conj xs => if P.g xs then 1 else 0
def P.g : List P → Bool
  | [] => true
  | p :: ps => P.f (.conj (p :: ps)) == 0
end
