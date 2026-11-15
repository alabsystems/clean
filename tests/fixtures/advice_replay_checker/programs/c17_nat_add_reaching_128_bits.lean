def two127 : Nat := 170141183460469231731687303715884105728

def main : IO Unit := do
  IO.println (toString (two127 + (two127 - 1)))
  IO.println (toString (two127 + two127))
