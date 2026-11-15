-- OPEN (design §5.4): the recursion goes through `Option O`, a
-- multi-constructor intermediate. Lean 4.8 accepts it by well-founded
-- recursion; Clean's lift refuses it. The fixed `k` keeps the block outside
-- Track AA (two binder-free members), so the lift is what decides it.
inductive O where
  | leaf : Nat → O
  | opt : Option O → O
  | many : List O → O
mutual
def O.f (k : Nat) : O → Nat
  | .leaf n => n + k
  | .opt o =>
    match o with
    | some x => O.f k x
    | none => 0
  | .many xs => O.fl k xs
def O.fl (k : Nat) : List O → Nat
  | [] => 0
  | x :: xs => O.f k x + O.fl k xs
end
theorem t : O.f 0 (.many [.opt (some (.leaf 2)), .leaf 1]) = 3 := by decide
