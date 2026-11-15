def main (args : List String) : IO UInt32 := do
  IO.println s!"argc={args.length}"
  return 3
