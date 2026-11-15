def xs : List Nat := [3, 1, 4, 1, 5, 9]

def main : IO Unit := do
  IO.println (toString (xs.take 5))
  IO.println (toString (xs.take 5).length)
  IO.println (toString xs.length)
