def main : IO Unit := do
  let x : Float := 2.5
  let y : Float := 4.0
  IO.println (toString (x * y).toUInt64)
  IO.println (if x + y > 3.0 then "gt" else "le")
  IO.println (toString (Float.ofNat 7).toUInt64)
