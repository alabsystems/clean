def main : IO Unit := do
  let a : Int := 10
  let b : Int := 3
  IO.println (toString (a / b))
  IO.println (toString (a % b))
  IO.println (toString (a + b))
  IO.println (toString (a * b))
  IO.println (toString (a - 20))
