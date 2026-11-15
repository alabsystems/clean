def main : IO Unit := do
  IO.println (toString ((255 : UInt8) + 1))
  IO.println (toString ((0 : UInt32) - 1))
  IO.println (toString (Char.ofNat 65))
  IO.println (toString ('z'.toNat))
  IO.println (toString ((10 : Int) / 3))
  IO.println (toString ((-7 : Int) % 3))
  IO.println (toString ((-7 : Int) / 2))
