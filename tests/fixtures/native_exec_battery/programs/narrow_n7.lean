def main (args : List String) : IO UInt32 := do
  if args.length > 5 then
    IO.println "big"
  else
    IO.println "small"
  return 0
