def two64 : Nat := 18446744073709551616

def main : IO Unit := do
  IO.println (toString ((two64 - 1) * (two64 - 1)))
  IO.println (toString (two64 * two64))
