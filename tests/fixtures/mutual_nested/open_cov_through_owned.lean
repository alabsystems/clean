-- OPEN (design §5.4, judge k7): a course-of-values call through an owned
-- slot — `P.f p` on the head of the `List P` field. Lean 4.8 accepts it by
-- well-founded recursion; Clean's structural lift refuses it. The fixed `k`
-- keeps the block outside Track AA (two binder-free members).
inductive P where
  | leaf : Nat → P
  | conj : List P → P
mutual
def P.f (k : Nat) : P → Nat
  | .leaf n => n + k
  | .conj [] => 0
  | .conj (p :: ps) => P.f k p + P.g k ps
def P.g (k : Nat) : List P → Nat
  | [] => 0
  | p :: ps => P.f k p + P.g k ps
end
theorem t : P.f 0 (.conj [.leaf 1, .leaf 2]) = 3 := by decide
