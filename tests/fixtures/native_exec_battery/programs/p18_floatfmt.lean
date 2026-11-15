def main : IO Unit := do
  IO.println (toString (1.5 : Float))
  IO.println s!"{(3.0 : Float)}"
  IO.println (repr "quote\"d")
  IO.println (repr 'c')
  IO.println (repr [some 1, none])
  IO.println (repr (1, "a"))
