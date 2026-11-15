-- `attribute [implemented_by fast] slow` AFTER `caller` was compiled. Lean
-- compiles each declaration as it is added, so `caller`'s code predates the
-- binding; it prints `2` here only because Lean's inliner copies `caller`
-- into `main`, compiled after the binding (`attr_implemented_by_order_noinline`
-- stops it and prints `3`).
def fast (n : Nat) : Nat := n + 1
def slow (n : Nat) : Nat := n + 2
def caller (n : Nat) : Nat := slow n
attribute [implemented_by fast] slow
def main : IO Unit := IO.println (toString (caller 1))
