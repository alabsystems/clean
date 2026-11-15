def main (args : List String) : IO Unit := do
  if args.length > 5 then IO.println "big" else IO.println "small"
