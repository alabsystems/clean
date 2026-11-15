-- `caller`'s code is fixed before the binding and is not inlined into
-- `main`, so Lean runs `slow`'s own body: `3`.
def fast (n : Nat) : Nat := n + 1
@[noinline] def slow (n : Nat) : Nat := n + 2
@[noinline] def caller (n : Nat) : Nat := slow n
attribute [implemented_by fast] slow
def main : IO Unit := IO.println (toString (caller 1))
