-- The command form before every caller, on a declaration small enough to be an
-- inline candidate (LCNF size at most `compiler.small`): Lean compiled `slow`
-- when it was added and copies that old body into `main`, `1`.
def fast (n : Nat) : Nat := Nat.add n 100
def slow (n : Nat) : Nat := n
attribute [implemented_by fast] slow
def main : IO Unit := IO.println (toString (slow 1))
