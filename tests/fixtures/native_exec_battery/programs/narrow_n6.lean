def main : IO Unit := do
  if false then IO.println "never" else pure ()
  IO.println "done"
