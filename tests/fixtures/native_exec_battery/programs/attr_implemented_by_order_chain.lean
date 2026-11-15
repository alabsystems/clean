-- A link added to a chain later: `caller` was compiled while `slow` ran
-- `middle` (`3`); `main`, compiled after `middle` gained its own binding,
-- runs `fastest` (`2`).
def fastest (n : Nat) : Nat := n + 1
def middle (n : Nat) : Nat := n + 2
@[implemented_by middle] def slow (n : Nat) : Nat := n + 3
@[noinline] def caller (n : Nat) : Nat := slow n
attribute [implemented_by fastest] middle
def main : IO Unit := do
  IO.println (toString (caller 1))
  IO.println (toString (slow 1))
