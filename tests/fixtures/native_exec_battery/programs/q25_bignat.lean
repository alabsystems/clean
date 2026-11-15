def main : IO Unit := do
  IO.println (toString (2 ^ 127 + 2 ^ 127))
  IO.println (toString (2 ^ 128))
