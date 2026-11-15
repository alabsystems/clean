-- G22 twin: the induction hypothesis takes `n` BEFORE `h0` (context order);
-- applying it the other way round is refused.
theorem ih_order_twin (xs : List Nat) (n : Nat) (h0 : xs.length = n) : xs.length = n := by
  induction xs generalizing n with
  | nil => exact h0
  | cons x rest ih =>
    have hi := ih rfl rest.length
    exact h0
