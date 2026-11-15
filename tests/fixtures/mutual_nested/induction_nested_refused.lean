-- Lean 4.8 refuses `induction` on a nested inductive: its default
-- eliminator has several motives.
inductive P where
  | leaf : Nat → P
  | conj : List P → P

theorem induction_nested (p : P) : True := by
  induction p with
  | leaf n => trivial
  | conj xs ih => trivial
