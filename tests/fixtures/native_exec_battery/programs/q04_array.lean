def main : IO Unit := do
  let a : Array Nat := #[5, 3, 8, 1, 9, 2]
  IO.println (toString a)
  IO.println (toString (a.push 7))
  IO.println (toString a.size)
  IO.println (toString (a.map (· * 2)))
  IO.println (toString (a.foldl (· + ·) 0))
  IO.println (toString a[2]!)
  IO.println (toString a.toList)
  IO.println (toString (a.contains 8))
  IO.println (toString a.reverse)
