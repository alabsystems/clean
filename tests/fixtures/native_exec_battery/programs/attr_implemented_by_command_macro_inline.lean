-- The command form on a `@[macro_inline]` declaration, before and after a
-- caller: Lean expands the body everywhere, `3` and `3`.
def fast (n : Nat) : Nat := Nat.add n 1
@[macro_inline] def slow (n : Nat) : Nat := Nat.add n 2
def before (n : Nat) : Nat := slow n
attribute [implemented_by fast] slow
def main : IO Unit := do
  IO.println (toString (before 1))
  IO.println (toString (slow 1))
