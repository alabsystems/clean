def main : IO Unit := do
  let xs := List.range 10
  IO.println xs
  IO.println (xs.filter (· % 3 == 0))
  IO.println (xs.map (· * xs.length))
  IO.println (List.foldl (· + ·) 0 [1, 2, 3, 4])
  IO.println (xs.zip (xs.map toString)).length
  IO.println ([3, 1, 2].mergeSort (· ≤ ·))
  IO.println (xs.take 3 ++ xs.drop 8)
  IO.println ([1, 2, 3].reverse)
  IO.println (xs.sum)
  IO.println ([[1, 2], [3]].flatten)
