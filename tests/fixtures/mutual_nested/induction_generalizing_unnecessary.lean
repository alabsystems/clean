-- Lean 4.8 refuses a `generalizing` argument that `induction` already
-- generalizes because it mentions the target.
theorem generalizing_unnecessary (xs : List Nat) (n : Nat) (h0 : xs.length = n) :
    xs.length = n := by
  induction xs generalizing h0 with
  | nil => exact h0
  | cons x rest ih => exact h0
