-- The entry itself was compiled before the binding: Lean runs `slow`'s own
-- body, `3`.
def fast (n : Nat) : Nat := n + 1
def slow (n : Nat) : Nat := n + 2
def main : IO Unit := IO.println (toString (slow 1))
attribute [implemented_by fast] slow
