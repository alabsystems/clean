-- The command form with every caller compiled after it: Lean runs `fast`
-- everywhere, `2`.
def fast (n : Nat) : Nat := n + 1
@[noinline] def slow (n : Nat) : Nat := n + 2
attribute [implemented_by fast] slow
@[noinline] def caller (n : Nat) : Nat := slow n
def main : IO Unit := IO.println (toString (caller 1))
