-- False twin of shared_slot_eval.lean: true only if `P.any` were wired to
-- `P.all` (`P.any [] = false`, `P.all [] = true`).
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

theorem e1_twin : P.eval (.disj []) = true := by decide
