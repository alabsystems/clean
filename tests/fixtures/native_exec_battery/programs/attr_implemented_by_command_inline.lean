-- The command form before every caller, on an `@[inline]` declaration: Lean
-- inlines the body it compiled before the binding into `main`, `3`.
def fast (n : Nat) : Nat := Nat.add n 1
@[inline] def slow (n : Nat) : Nat := Nat.add n 2
attribute [implemented_by fast] slow
def main : IO Unit := IO.println (toString (slow 1))
