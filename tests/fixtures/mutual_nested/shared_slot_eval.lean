-- Brick B2, shared slot: two members own `List P` (trust-ir `Pred.denoteAll` /
-- `Pred.denoteAny`, Pred.lean:396), so its motive is a `PProd` pair.
inductive P where
  | leaf : Nat → P
  | conj : List P → P
  | disj : List P → P

mutual
def P.eval : P → Bool
  | .leaf n => n == 0
  | .conj xs => P.all xs
  | .disj xs => P.any xs
def P.all : List P → Bool
  | [] => true
  | p :: ps => P.eval p && P.all ps
def P.any : List P → Bool
  | [] => false
  | p :: ps => P.eval p || P.any ps
end

theorem e1 : P.eval (.conj [.leaf 0, .disj [.leaf 1, .leaf 0]]) = true := by decide
theorem e2 : P.eval (.disj [.leaf 1, .leaf 0]) = true := by decide
