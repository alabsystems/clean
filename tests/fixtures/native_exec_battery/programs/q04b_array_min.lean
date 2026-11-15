def main : IO Unit := do
  let a : Array Nat := #[5, 3, 8]
  IO.println (toString a.size)
  IO.println (toString (a.push 7).size)
  IO.println (toString (a.foldl (· + ·) 0))
  IO.println (toString a.toList)
