def main : IO Unit := do
  let s := "Hello, World"
  IO.println s.length
  IO.println (s ++ "!")
  IO.println s.toUpper
  IO.println s.toLower
  IO.println (s.splitOn ", ")
  IO.println (", ".intercalate ["a", "b", "c"])
  IO.println (String.join ["x", "y", "z"])
  IO.println (String.mk s.toList.reverse)
  IO.println (s.drop 7)
  IO.println (s.take 5)
  IO.println ("42".toNat?)
  IO.println ("abc".toNat?)
  IO.println s!"len={s.length} first={s.get 0}"
  IO.println ("  trim me  ".trim)
  IO.println (s.contains 'W')
  IO.println ("héllo".length)
  IO.println ("héllo".utf8ByteSize)
