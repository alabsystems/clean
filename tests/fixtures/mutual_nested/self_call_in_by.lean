-- Gap G69 (OPEN): a single recursive theorem whose self-call sits inside a
-- `by` block. trust-ir's class (88) rows recurse this way
-- (`replicate_get?_of_lt`, `List_get?_set_eq_self`, …); Clean's recursion
-- detection does not look into tactic blocks.
theorem single_by : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | n + 1 => by exact congrArg (· + 1) (single_by n)
