def main : IO Unit := do
  let n : Int := -17
  IO.println (toString (n / 5))
  IO.println (toString (n % 5))
  IO.println (toString (Int.toNat (n * n)))
  IO.println (toString n.natAbs)
