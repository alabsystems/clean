def main (args : List String) : IO UInt32 := do
  IO.println s!"argc={args.length}"
  for a in args do
    IO.println a
  return 3
