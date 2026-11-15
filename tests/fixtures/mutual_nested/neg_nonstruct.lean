-- Refused by Lean 4.8: `P.g (xs ++ xs)` is not on a subterm (design §6.3).
-- (Result types differ, so the block is not Track AA's `T → R` / `C T → R`
-- pair and reaches the structural lift.)
inductive P where
  | leaf : Nat → P
  | conj : List P → P
mutual
def P.f : P → Nat
  | .leaf n => n
  | .conj xs => if P.g (xs ++ xs) then 1 else 0
def P.g : List P → Bool
  | [] => true
  | p :: ps => P.f p == 0 && P.g ps
end
