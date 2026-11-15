def main : IO Unit := do
  let xs := List.range 10
  IO.println (toString xs)
  IO.println (toString (xs.filter (· % 3 == 0)))
  IO.println (toString (xs.map (· * 10)))
  IO.println (toString (List.foldl (· + ·) 0 [1, 2, 3, 4]))
  IO.println (toString (xs.take 3 ++ xs.drop 8))
  IO.println (toString [1, 2, 3].reverse)
