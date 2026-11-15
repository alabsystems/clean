def main : IO Unit := do
  let s := "Hello, World"
  IO.println (toString s.length)
  IO.println (s ++ "!")
  IO.println s.toUpper
  IO.println s.toLower
  IO.println (toString (s.splitOn ", "))
  IO.println (", ".intercalate ["a", "b", "c"])
  IO.println (String.join ["x", "y", "z"])
  IO.println (s.drop 7)
  IO.println (s.take 5)
  IO.println (toString ("42".toNat?))
  IO.println s!"len={s.length}"
  IO.println (toString (s.contains 'W'))
  IO.println (toString ("héllo".length))
  IO.println (toString ("héllo".utf8ByteSize))
