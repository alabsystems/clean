def main (args : List String) : IO UInt32 := do
  for a in args do
    IO.println a
  return 3
