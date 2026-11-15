def counter : StateM Nat Unit := do
  modify (· + 1)
  modify (· * 10)

def main : IO Unit := do
  let ((), s) := counter.run 4
  IO.println (toString s)
