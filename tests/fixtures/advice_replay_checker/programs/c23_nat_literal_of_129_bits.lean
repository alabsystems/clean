def two128 : Nat := 340282366920938463463374607431768211456

def main : IO Unit := do
  IO.println (toString (two128 - 1))
  IO.println (toString two128)
