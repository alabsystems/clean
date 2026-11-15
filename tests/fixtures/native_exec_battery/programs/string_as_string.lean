def main : IO Unit := do
  IO.println ['a', 'b'].asString
  IO.println (toString ("abc" == String.mk ['a', 'b', 'c']))
