-- `@[macro_inline]` with `@[implemented_by]` on the declaration: Lean expands
-- the body at every call site and never runs `fast`, `3`.
def fast (n : Nat) : Nat := Nat.add n 1
@[macro_inline, implemented_by fast] def slow (n : Nat) : Nat := Nat.add n 2
def caller (n : Nat) : Nat := slow n
def main : IO Unit := do
  IO.println (toString (slow 1))
  IO.println (toString (caller 1))
