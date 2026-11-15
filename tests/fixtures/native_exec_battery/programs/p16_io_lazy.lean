def main : IO Unit := do
  let a := IO.println "A"
  IO.println "B"
  a
  a
  if false then IO.println "never" else pure ()
  let acts : List (IO Unit) := [IO.println "x1", IO.println "x2"]
  IO.println "before"
  for act in acts.reverse do act
