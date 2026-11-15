def f (o : Option Nat) : Option Nat := do
  let x ← o
  pure (x + 1)

def main : IO Unit := do
  IO.println (toString ((f none).getD 0))
  IO.println (toString ((f (some 4)).getD 0))
